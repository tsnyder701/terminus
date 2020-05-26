(ns covid.util)

;; kvmap transforms a map by applying kf to each key and vf to each value
;; kf should be one-to-one or the output is undefined
(defn kvmap
  ([kf vf m]
   (into {} (for [[k v] m]
              [(kf k) (vf v)]))))

(defn nmap
  ([f & maps-or-vals]
   (if (empty? maps-or-vals)
     (f)
     (if (not (map? (first maps-or-vals)))
       (apply f maps-or-vals)
       (let [ms maps-or-vals
             keyset (into #{} (mapcat keys ms))
             missing (Object.)]
         (into {} (for [k keyset
                        :let [vs (map #(get %1 k missing) ms)]]
                    [k (apply nmap f (filter #(not= missing %) vs))])))))))

(defn cmap [f-map m1 m2]
  (for [[k1 v1] m1
        [k2 v2] m2]
    ((f-map k1 k2) v1 v2)))

(defn nreduce
  ([f-merge f-val map-or-vals]
   (if (not (map? map-or-vals))
     (f-val map-or-vals)
     (reduce f-merge (map (partial nreduce f-merge f-val) (vals map-or-vals))))))

(defn nget [m key & [default]]
  (if (not (map? m))
    m
    (if (map? (val (first m)))
      (kvmap identity #(nget % key) m)
      (get m key default))))

;; normalize takes a map of keys to relative proprotions and returns a map
;; of keys to probabilities, suitable for use with draw
(defn normalize [m]
  (let [s (reduce + (vals m))]
    (if (zero? s)
      (kvmap identity (constantly (/ (count m))) m)
      (kvmap identity #(/ %1 s) m))))

(defn avg
  ([x] (/ (reduce + 0.0 x) (float (count x))))
  ([x y] (let [x&y (filter (fn [[x y]] (and x y)) (map vector x y))
               top (reduce + 0.0 (map (partial apply *) x&y))
               bottom (reduce #(+ %1 (second %2)) 0.0 x&y)]
           (if (zero? bottom)
             (if (zero? top)
               ##NaN
               (if (pos? top) ##Inf (- ##Inf)))
             (/ top bottom)))))

(defn diffs [aggs & [steps]]
  (let [steps (or steps 1)])
  (into (sorted-map)
        (map vector
             (drop (int (/ (inc steps) 2)) (keys aggs))
             (map #(/ (- %1 %2) steps) (drop steps (vals aggs)) (vals aggs)))))
