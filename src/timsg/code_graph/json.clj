(ns timsg.code-graph.json
  (:require [arcadiatech.intervention-api.utils :as u]
            [arcadia.internal.map-utils :as mu]
            [arcadia.debug :refer [break]])
  (:import [System.Text StringBuilder]))

;; we seem not to have built-in access to any real JSON parsing libraries,
;; and I don't want to try to write sound string escape logic right now,
;; so I'm just going to wrap strings in quotes and send them unescaped.
;; We should have no need for nested strings anyway so long as we're
;; just using this to send specifications to blockly

;; allowed:
;; maps
;; vectors
;; strings
;; numbers
;; (note that this does not include keywords)
(defn json [data]
  (let [sb (StringBuilder.)]
    (letfn [(append [^String s]
              (.Append sb s))
            (step [data]
              (cond
                (map? data)
                (do (append "{")
                    (reduce-kv
                      (fn [i k v]
                        (step k)
                        (append ":")
                        (step v)
                        (when (< i (dec (count data)))
                          (append ","))
                        (inc i))
                      0
                      data)
                    (interpose ",")
                    (append "}"))
                
                (string? data)
                (do (append "\"")
                    ;; some unsound quoting here, just to support our XML stuff
                    ;; might be pretty inefficient though, given how many strings
                    ;; we expect
                    (append (clojure.string/replace data "\"" "\\\""))                    
                    (append "\""))

                ;; TODO: not sure this will format numbers correctly
                (number? data)
                (append (.ToString (double data)))

                (vector? data)
                (do (append "[")
                    (reduce
                      (fn [i x]
                        (step x)
                        (when (< i (dec (count data)))
                          (append ","))
                        (inc i))
                      0
                      data)
                    (append "]"))

                (nil? data)
                (append "null")

                (boolean? data)
                (append (if data "true" "false"))

                :else (do
                        (break json)
                        (throw
                          (Exception.
                            "Unconvertable type, must be map, string, number, nil, boolean, or vector.")))))]
      (step data)
      (.ToString sb))))
