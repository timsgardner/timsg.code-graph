(ns timsg.code-graph.long-dispatch
  (:require [arcadia.internal.macro :as macro]
            [arcadiatech.intervention-api.utils :as u])
  (:refer-clojure :exclude [def defonce extend]))

;; I guess it should return a keyed map rather than a vector

(defprotocol IDispatchRef
  (get-ref [this]))

;; always takes a self argument
(defn long-dispatch []
  (let [ref (atom {})]
    (macro/meval ;; <- note! following evals at compile-time
      (let [argslists (reductions conj [] (take 18 (macro/classy-args)))
            impls (for [argslist argslists]
                    `(~argslist
                      (reduce-kv (fn [acc# k# {:keys [pred# f#]}]
                                   (if (pred# ~'this ~@argslist)
                                     (assoc acc# k# (f# ~'this ~@argslist))
                                     acc#))
                        {}                        
                        @~'ref)))
            end-impl (let [args-base (-> (vec (take 19 (cons 'self (macro/classy-args)))))
                           argslist (conj args-base '& 'rest)
                           argslist' (conj args-base 'rest)]
                       `(~argslist
                         (reduce-kv (fn [acc# k# {:keys [pred# f#]}]
                                      (if (apply pred# ~'this ~@argslist')
                                        (conj acc# k# (apply f# ~'this ~@argslist'))
                                        acc#))
                           {}
                           @~'ref)))]
        `(proxy [clojure.lang.AFn timsg.code_graph.long_dispatch.IDispatchRef] []
           (get-ref [this#] ref)
           (invoke
             ~@impls
             ~end-impl))))))

(defmacro def [name]
  `(def ~name (long-dispatch)))

(defmacro defonce [name]
  `(clojure.core/defonce ~name (long-dispatch)))

(defn extend [d key pred f]
  (swap! (get-ref d) assoc key {:pred pred, :f f})
  d)

(defmacro def-extension [^clojure.lang.Symbol name, key, pred-body, f-body]
  (let [[pred-args] pred-body
        [f-args] f-body]
    (assert (vector? pred-args))
    (assert (vector? f-args))
    (assert (= (count pred-args) (count f-args))))
  (let [name-ns (or (some-> (.Namespace name) symbol ((ns-aliases *ns*)) ns-name (.Name))
                    (.Namespace name))
        name-name (.Name name)
        fs-name (str name-ns)]
    (let [pred `(fn ~(symbol (str fs-name "_pred")) ~@pred-body)
          f `(fn ~(symbol (str fs-name "_f")) ~@f-body)]
      `(extend ~name ~key ~pred ~f))))
