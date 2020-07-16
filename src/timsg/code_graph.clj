(ns timsg.code-graph
  (:require [clojure.spec.alpha :as s]
            [clojure.tools.analyzer :as ana]
            [clojure.tools.analyzer.ast :as ast]
            [clojure.tools.analyzer.env :as env]
            [clojure.tools.analyzer.passes :as passes]
            [clojure.tools.analyzer.passes.elide-meta :as elide-meta]
            [arcadia.debug :refer [break]]
            [magic.analyzer :as mana]
            [arcadiatech.intervention-api.utils :as u] ;; TODO: remove this dep
            [arcadiatech.intervention-api.graph-utils :as gu]
            [flybot.ports.ubergraph.core :as uber]
            [clojure.clr.io :as io]
            [timsg.code-graph.json :as json])
  (:use clojure.repl)
  (:import [System.IO FileInfo DirectoryInfo]
           [clojure.lang LineNumberingTextReader]
           AnalyzerTiming))

(s/def ::mention-kind any?)

(s/def ::mention-target any?)

(s/def ::mention
  (s/keys
    :req [::mention-kind
          ::mention-target]))

(s/def ::mentions
  (s/every ::mention :kind set?))

(s/def ::ast any?) ;; really it's an analyzer ast

(s/def ::def-datum
  (s/keys
    :req [::ast ::mentions ::def-kind]))

(s/def ::def-data
  (s/every ::def-datum))

(s/def ::top-form-datum
  (s/keys
    :req [::ast
          ::def-data]))

(s/def ::top-form-data
  (s/every ::top-form-datum))

(s/def ::ns symbol?)

(s/def ::namespace-datum
  (s/keys
    :req [::top-form-data
          ::ns]))

;; ============================================================
;; utils

(def timings (new AnalyzerTiming))

(def ^:dynamic *rig-for-timing* true)

(defn rig-for-timing [k f]
  (if *rig-for-timing*
    (fn
      ([]
       (.StartCall timings k)
       (let [result (f)]
         (.StopCall timings k)
         result))
      ([a]
       (.StartCall timings k)
       (let [result (f a)]
         (.StopCall timings k)
         result))
      ([a b]
       (.StartCall timings k)
       (let [result (f a b)]
         (.StopCall timings k)
         result))
      ([a b c]
       (.StartCall timings k)
       (let [result (f a b c)]
         (.StopCall timings k)
         result))
      ([a b c d]
       (.StartCall timings k)
       (let [result (f a b c d)]
         (.StopCall timings k)
         result))
      ([a b c d e]
       (.StartCall timings k)
       (let [result (f a b c d e)]
         (.StopCall timings k)
         result))
      ([a b c d e & args]
       (.StartCall timings k)
       (let [result (apply f a b c d e args)]
         (.StopCall timings k)
         result)))
    f))

;; suspicious of some functions
;; note this is irreversible and dangerous
(defn rig-var-for-timing [var]
  (let [ns (ns-name (.Namespace var))
        name (.Symbol var)]
    (intern ns name (rig-for-timing
                      (symbol (str ns) (str name))
                      (var-get var)))))

(defmacro rig-for-timing-mac [f]
  `(rig-for-timing (quote ~f) ~f))

(defn elide-all-meta [ast]
  (binding [elide-meta/elides {:all any?}]
    (elide-meta/elide-meta ast)))

(defn other-analyze
  ([form] (other-analyze form (mana/empty-env)))
  ([form env] (other-analyze form env mana/run-passes))
  ([form env passes-fn]
   (binding [ana/macroexpand-1 (rig-for-timing-mac mana/macroexpand-1)
             ana/create-var    (fn [sym env]
                                 (doto (intern (:ns env) sym)
                                   (reset-meta! (meta sym))))
             ana/parse         (rig-for-timing-mac mana/parse)
             ana/var?          var?]
     (env/with-env (mana/global-env)
       ((rig-for-timing-mac ana/analyze) form env)))))

;; ============================================================
;; analysis

(defn mark-macros
  "Mark macro ast nodes"
  {:pass-info {:walk :post,
               :depends #{}}}
  [{:keys [raw-forms],
    {:keys [ns]} :env,
    :as ast}]
  (if-let [macro-symbol (and raw-forms
                             (list? (first raw-forms))
                             (ffirst raw-forms))]    
    (let [ns-obj (find-ns ns)
          macro-var (ns-resolve ns-obj macro-symbol)]
      (assert ns-obj (str "Cannot find namespace for '" ns))
      (assoc ast ::macro {::var macro-var}))
    ast))

(def mnf-counter (atom 0))
(def mnf-vars (atom #{}))

(defn mark-ns-forms 
  {:pass-info {:walk :post
               :depends #{#'mark-macros}}}
  [{{:keys [::var]} ::macro,
    :as ast}]
  (swap! mnf-counter inc)
  (swap! mnf-vars conj var)
  (if (= var #'clojure.core/ns)    
    (let [[[_ ns-name]] (:raw-forms ast)]
      (assoc ast ::ns-form {::ns ns-name}))
    ast))

;; schedule seems bugged
(defn mark-walk [ast]
  (-> ast
      (ast/update-children mark-walk)
      (mark-macros)
      (mark-ns-forms)))

;; ============================================================
;; make the data

;; if we want open dispatch need to do some innovating.
;; No time for that shit now, just make it closed
(defn ast-to-mention [{:keys [op] :as ast}]
  (cond
    (= op :var)
    {::mention-kind :var
     ::mention-target (:var ast)}))

(defn ast-def-kind [{:keys [op] :as ast}]
  (cond
    (= op :def)
    (cond
      (= (some-> (::macro ast) ::var)
         #'defn)
      :defn)))

(defn ignore-ast? [{:keys [op] :as ast}]
  (boolean
    (#{:host-call :host-field :host-interop :maybe-class :maybe-host-form} op)))

;; sometimes :raw-forms isn't actually a seq of successive expansions of the original form.
;; this is a stupid bug.
(defn sub-form-filter [ast sub-forms]
  ;;(break sub-form-filter-top)
  (when-let [form (and (not (ignore-ast? ast))
                       (or (when-let [rd (:raw-forms ast)]
                             (when-let [frm (and (seq? rd) (first rd))]
                               (when (seq? frm))
                               frm))
                           (and (contains? ast :form)
                                (:form ast))))]
    (contains? sub-forms form)))

(defn definition-ast-to-mentions [ast sub-forms]
  (->> (tree-seq any? ast/children ast)
       (filter #(sub-form-filter % sub-forms))
       (keep ast-to-mention)
       set))

(defn ast-to-def-datum [ast sub-forms]
  (when-let [def-kind (ast-def-kind ast)]
    {::def-kind def-kind
     ::ast ast
     ::mentions (definition-ast-to-mentions ast sub-forms)}))

;; ast should be a top-level form
;; why are we even getting here for non-definitions?
;; returns a ::top-form-datum
(defn definition-ast-to-def-data [{:keys [form
                                          raw-forms]
                                   :as ast}]
  (when (ast-def-kind ast)
    (let [sub-forms (set
                      (tree-seq coll? seq
                        (if raw-forms
                          (first raw-forms)
                          form)))]
      {::ast ast
       ::def-data (->> (tree-seq (complement ast-def-kind) ast/children ast) ;; the branch? function here is to halt descent
                       ;; only want those that occur in the sub-forms
                       (filter #(sub-form-filter % sub-forms))
                       (keep #(ast-to-def-datum % sub-forms))
                       vec)})))

(defn analyze-form [ns-name form]
  (let [env (assoc (mana/empty-env) :ns ns-name)]
    (mark-walk
      (elide-all-meta ;; TODO: or not. should probably remove this onfce things settle down
        (other-analyze form env)))))

(defn forms-to-asts [starting-namespace forms]
  (time
    (loop [ns starting-namespace
           forms forms
           asts []]
      (if-let [[form & forms] forms]
        (let [ast (analyze-form ns form)
              ns (or (some-> (get ast ::ns-form) (get ::ns)) ;; assumes ns form is at top level. It usually is.
                     ns)]
          (recur ns forms (conj asts ast)))
        asts))))

(defn ast-ns [ast]
  (or (some-> (get ast ::ns-form) (get ::ns))
      (-> (get ast :env) (get :ns))))

(defn forms-to-data [starting-namespace forms]
  (let [ns-parts (->> (forms-to-asts starting-namespace forms)
                      (partition-by ast-ns)
                      doall)]
    (vec
      (for [[ast :as asts] ns-parts
            :let [ns (ast-ns ast)
                  top-form-data (vec (keep definition-ast-to-def-data asts))]]
        {::ns ns
         ::top-form-data top-form-data}))))

;; ============================================================
;; make the graph

(defn var-sym [^clojure.lang.Var var]
  (symbol
    (str (ns-name (.Namespace var)))
    (str (.get_sym var))))

(u/defmulti-once mention-target-graph-node ::mention-kind)

(u/defmethod mention-target-graph-node :var [mention]
  (::mention-target mention))

(defn definition-graph-node-attrs [def-datum]
  ;; TODO: put something cool here later
  {})

(u/defmulti-once definition-graph-node ::def-kind)

(u/defmethod definition-graph-node :defn [{:keys [::ast]}]
  (:var ast))

;; pattern match would be nice here
;; REALLY don't want to deal with that yak right now,
;; so just have it dispatch on the target I guess
(u/defmulti mention-edge-attrs
  (fn [def-datum mention]
    (::mention-kind mention)))

(u/defmethod mention-edge-attrs :var [def-datum mention]
  {})

(defn mention-edge [def-datum mention]
  (let [node (definition-graph-node def-datum)
        mention-target (mention-target-graph-node mention)]
    [node, mention-target, (mention-edge-attrs def-datum mention)]))

(defn namespace-datum-to-graph [namespace-datum]
  (apply uber/multidigraph
    (let [{:keys [::top-form-data]} namespace-datum]
      (for [{:keys [::def-data]} top-form-data
            {:keys [::mentions] :as def-datum} def-data]
        (let [node (definition-graph-node def-datum)
              node-attrs (definition-graph-node-attrs def-datum)
              edges (for [mention mentions]
                      (mention-edge def-datum mention))]
          (-> (apply uber/multidigraph edges)
              (uber/add-nodes node node-attrs)))))))

;; ============================================================
;; forms from files

(defn read-all
  [file]
  (with-open [rdr (-> file io/text-reader LineNumberingTextReader.)]
    (loop [forms []]
      (let [form (try (read rdr) (catch Exception e nil))] ;; why the exception eater?
        (if form
          (recur (conj forms form))
          forms)))))

(defn fileinfos-to-graph [fileinfos]
  (->> fileinfos
       (mapcat read-all)
       (forms-to-data 'user)
       (map namespace-datum-to-graph)
       (apply uber/multidigraph)))

;; ============================================================
;; spit to svg

(defn spit-code-graph-to-svg [g]
  (comment
    (let []
      (-> g
          ()
          (uber/viz-graph {:format :svg})))))

;; ============================================================
;; spit to json

(defn stringify-keyword [^clojure.lang.Keyword kw]
  (if-let [ns (.Namespace kw)]
    (str ns "/" (.Name kw))
    (.Name kw)))

(defn format-for-json [g]
  (clojure.walk/postwalk #(if (keyword? % (stringify-keyword %)) %)
    (uber/ubergraph->edn g)))


