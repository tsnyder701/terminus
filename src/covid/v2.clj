(ns covid.v2
  (:require [incanter.core :as i]
            [incanter.charts :as ic]
            [incanter.distributions :as id]
            [incanter.stats :as is]
            [clojure.set :as set])
  (:import [java.awt Color]))

(def isolation-severity 0.3)
(def death-rate 0.03)
(def hospitalization-rate 0.25)

(def halt-flag (atom false))

(defn kvmap [kf vf m]
  (into {} (for [[k v] m]
             [(kf k) (vf v)])))

(defn normalize [m]
  (let [s (reduce + (vals m))]
    (kvmap identity #(/ %1 s) m)))

(def age-demo (normalize {0 40, 1 42, 2 43, 3 41, 4 41, 5 42, 6 36, 7 20, 8 8, 9 1}))
(def age-severity {0 [10/19 19/10], 1 [50/73 73/50], 2 [5/8 8/5], 3 [3/4 4/3], 4 [25/32 32/25], 5 [15/16 16/15], 6 [9/8 8/9], 7 [11/8 8/11], 8 [7/4 4/7], 9 [8/4 4/8]})
(def age-sex-severity (kvmap identity (partial apply id/beta-distribution)
                             (for [[age [a b]] age-severity
                                   [sex scale] [[:male 1.06] [:female 0.94]]]
                               [[age sex] [(* a scale) (/ b scale)]])))
(def household-children (normalize {1 14081, 2 12853, 3 4500, 4 2000, 5 400, 6 100}))
(def household-size (normalize {1 28, 2 34, 3 15, 4 13, 5 6, 6 2, 7 1, 8 0.2}))
(def households (normalize {#{:mother :father :children} 20, #{:man :woman} 28,
                            #{:mother :children} 7, #{:woman :parent} 6,
                            #{:father :children} 2, #{:man :parent} 2,
                            #{:man} 12, #{:man :other} 4,
                            #{:woman} 15, #{:woman :other} 3}))
(def identity-ages {:mother (normalize {2 20, 3 35, 4 35, 5 30, 6 5, 7 1}),
                    :father (normalize {2 15, 3 38, 4 38, 5 35, 6 10, 7 2}),
                    :man (normalize {1 5, 2 30, 3 34, 4 30, 5 25, 6 20, 7 10, 8 4, 9 1}),
                    :woman (normalize {1 3, 2 30, 3 34, 4 30, 5 25, 6 22, 7 12 8 5, 9 2}),
                    :parent (normalize {4 10, 5 20, 6 30, 7 30, 8 20, 9 5})
                    :children (normalize {0 50, 1 40})
                    :other (normalize {2 43, 3 41, 4 41, 5 42, 6 36, 7 20, 8 8, 9 1})})
(def identity-sexes {:mother {:female 1},
                     :father {:male 1},
                     :man {:male 1},
                     :woman {:female 1},
                     :parent {:male 1/2, :female 1/2},
                     :children {:male 1/2, :female 1/2},
                     :other {:male 1/2, :female 1/2}})

(defn draw [m]
  (or (reduce #(if (< %1 (second %2))
                 (reduced (first %2))
                 (- %1 (second %2)))
              (rand)
              m)
      (first (last m))))

(defn make-actors [n cluster-types]
  (loop [i 0
         hh-id 0
         actors []]
    (if (>= i n)
      (vec actors)
      (let [x (id/draw (id/normal-distribution))
            y (id/draw (id/normal-distribution))
            hh (draw households)
            hh-adults (disj hh :children)
            num-children (if (contains? hh :children) (draw household-children) 0)
            hh-cts (vec (for [ct cluster-types
                              :when (= :household (:level ct))
                              _ (range (draw (:multiplicity ct)))]
                          [(:type ct) (:name (draw (:subtype ct)))]))
            hh-cts (conj hh-cts [:household (keyword (str "hh" hh-id))])
            adult-cts (apply merge-with into
                        (for [ct cluster-types
                              :when (= :hh-adult (:level ct))
                              _ (range (draw (:multiplicity ct)))]
                          {(rand-int (count hh-adults)) [[(:type ct) (:name (draw (:subtype ct)))]]}))
            children-cts (vec (for [ct cluster-types
                                    :when (= :hh-children (:level ct))
                                    _ (range (draw (:multiplicity ct)))]
                                [(:type ct) (:name (draw (:subtype ct)))]))]
        (recur (+ i (count hh-adults) num-children)
               (inc hh-id)
               (into actors
                 (concat (for [j (range (count hh-adults))
                               :let [id (nth (seq (disj hh :children)) j)
                                     age (draw (identity-ages id))
                                     sex (draw (identity-sexes id))
                                     severity (id/draw (age-sex-severity [age sex]))
                                     cts (into hh-cts (get adult-cts j))
                                     cts (into cts (for [ct cluster-types
                                                         :when (= :individual (:level ct))
                                                         _ (range (draw ((:multiplicity-by-age ct) age)))]
                                                     [(:type ct) (:name (draw (:subtype ct)))]))]]
                           {:loc [x y], :age age, :sex sex, :severity severity,
                            :cluster-names cts})
                         (for [j (range num-children)
                               :let [age (draw (identity-ages :children))
                                     sex (draw (identity-sexes :children))
                                     severity (id/draw (age-sex-severity [age sex]))
                                     cts (into hh-cts children-cts)
                                     cts (into cts (for [ct cluster-types
                                                         :when (= :individual (:level ct))
                                                         x (range (draw ((:multiplicity-by-age ct) age)))]
                                                     [(:type ct) (:name (draw (:subtype ct)))]))]]
                           {:loc [x y], :age age, :sex sex,
                            :severity severity, :cluster-names cts}))))))))

(defn round-location [[x y] d]
  [(/ (int (* x d)) d) (/ (int (* y d)) d)])

(defn index-locations [objects d]
  (reduce #(update %1 (round-location (:loc %2) d) conj %2) {} objects))

(defn abs [x]
  (if (neg? x)
    (- x)
    x))

(defn dist [[x1 y1] [x2 y2]]
  (+ (abs (- x1 x2)) (abs (- y1 y2))))

(defn make-clusters [actors cluster-types]
  (let [actors (vec (map-indexed #(assoc %2 :id %1) actors))
        ckpt 1
        ckpt (do (println "mc" ckpt) (inc ckpt))
        uniq-locs (for [[a1 a2] (map vector actors (concat [nil] actors))
                        :let [l1 (:loc a1)
                              l2 (:loc a2)]
                        :when (not= l1 l2)]
                    l1)
        hh (mapv vector (range) uniq-locs)
        cluster-types (conj cluster-types {:type :household, :level :household, :multiplicity {1 1},
                                           :locality [0],
                                           :subtype (into {}
                                                          (for [[hh-id loc] hh]
                                                            [{:name (keyword (str "hh" hh-id)),
                                                               :count 1,
                                                               :loc loc} (/ (count hh))]))})
        clusters (for [ct cluster-types
                       cst (keys (:subtype ct))
                       i (range (:count cst))
                       :let [x (id/draw (id/normal-distribution))
                             y (id/draw (id/normal-distribution))
                             _ (if (= :hh0 (:name cst)) (println cst))]]
                   {:type (:type ct), :name [(:type ct) (:name cst)], :instance i,
                    :loc (or (:loc cst) [x y])})
        clusters (mapv #(assoc %1 :id %2) clusters (range))
        ckpt (do (println "mc" ckpt) (inc ckpt))
        hh-clusters (into {} (for [c clusters
                                   :when (= :household (:type c))]
                               [(:loc c) (:id c)]))
        o-clusters (vec (filter #(not= :household (:type %)) clusters))
        clusters-by-name (kvmap identity #(mapv :id %) (group-by :name o-clusters))
        actors-by-cell (index-locations actors 10)
        ckpt (do (println "mc" ckpt) (inc ckpt))
        cluster-distances-by-cell-name (into {}
                                         (for [cell (keys actors-by-cell)]
                                           [cell (into {}
                                                   (for [[name ids] clusters-by-name
                                                         :when (not= :household (first name))]
                                                     [name
                                                      (vec
                                                       (sort
                                                        (for [id ids
                                                              :let [loc (get-in clusters [id :loc])]]
                                                          [(apply +  cell loc) id])))]))]))
        ckpt (do (println "mc" ckpt) (inc ckpt))
        ct-by-type (into {} (map vector (map :type cluster-types) cluster-types))
        ckpt (do (println "mc" ckpt) (inc ckpt))
        actor-clusters (doall (for [[cell cell-actors] actors-by-cell
                                    :let [cdbn (cluster-distances-by-cell-name cell)]
                                    a cell-actors
                                    [ct :as cn] (:cluster-names a)
                                    :let [cluster (if (= ct :household)
                                                    (hh-clusters (:loc a))
                                                    (let [sorted-clusters (cdbn cn)
                                                          ci (int (* (count sorted-clusters)
                                                                     (id/draw (:locality (ct-by-type ct)))))]
                                                      (second (sorted-clusters ci))))]]
                                [(:id a) cluster]))
        ckpt (do (println "mc" ckpt) (inc ckpt))
        ac-by-actor (kvmap identity #(mapv second %) (group-by first actor-clusters))
        ac-by-cluster (kvmap identity #(mapv first %) (group-by second actor-clusters))
        ckpt (do (println "mc" ckpt) (inc ckpt))
        actors (reduce #(assoc-in %1 [(first %2) :clusters] (second %2)) actors ac-by-actor)
        ckpt (do (println "mc" ckpt) (inc ckpt))
        clusters (reduce #(assoc-in %1 [(first %2) :actors] (second %2)) clusters ac-by-cluster)]
    [actors clusters cluster-types]))

(defn make-actor-clusters [actors cluster-types]
  (let [actors (vec (map-indexed #(assoc %2 :id %1) actors))
        ckpt 1
        ckpt (do (println "mc" ckpt) (inc ckpt))
        uniq-locs (for [[a1 a2] (map vector actors (concat [nil] actors))
                        :let [l1 (:loc a1)
                              l2 (:loc a2)]
                        :when (not= l1 l2)]
                    l1)
        hh (mapv vector (range) uniq-locs)
        cluster-types (conj cluster-types {:type :household, :level :household, :multiplicity {1 1},
                                           :locality [0],
                                           :subtype (into {}
                                                          (for [[hh-id loc] hh]
                                                            [{:name (keyword (str "hh" hh-id)),
                                                               :count 1,
                                                               :loc loc} (/ (count hh))]))})
        clusters (for [ct cluster-types
                       cst (keys (:subtype ct))
                       i (range (:count cst))
                       :let [x (id/draw (id/normal-distribution))
                             y (id/draw (id/normal-distribution))
                             _ (if (= :hh0 (:name cst)) (println cst))]]
                   {:type (:type ct), :name [(:type ct) (:name cst)], :instance i,
                    :loc (or (:loc cst) [x y])})
        clusters (mapv #(assoc %1 :id %2) clusters (range))
        ckpt (do (println "mc" ckpt) (inc ckpt))
        hh-clusters (into {} (for [c clusters
                                   :when (= :household (:type c))]
                               [(:loc c) (:id c)]))
        o-clusters (vec (filter #(not= :household (:type %)) clusters))
        clusters-by-name (kvmap identity #(mapv :id %) (group-by :name o-clusters))
        actors-by-cell (index-locations actors 10)
        ckpt (do (println "mc" ckpt) (inc ckpt))
        cluster-distances-by-cell-name (into {}
                                         (for [cell (keys actors-by-cell)]
                                           [cell (into {}
                                                   (for [[name ids] clusters-by-name
                                                         :when (not= :household (first name))]
                                                     [name
                                                      (vec
                                                       (sort
                                                        (for [id ids
                                                              :let [loc (get-in clusters [id :loc])]]
                                                          [(dist cell loc) id])))]))]))
        ckpt (do (println "mc" ckpt) (inc ckpt))
        ct-by-type (into {} (map vector (map :type cluster-types) cluster-types))
        ckpt (do (println "mc" ckpt) (inc ckpt))
        actor-clusters (for [[cell cell-actors] actors-by-cell
                             :let [cdbn (cluster-distances-by-cell-name cell)]
                             a cell-actors
                             [ct :as cn] (:cluster-names a)
                             :let [cluster (if (= ct :household)
                                             (hh-clusters (:loc a))
                                             (let [sorted-clusters (cdbn cn)
                                                   ci (int (* (count sorted-clusters)
                                                              (id/draw (:locality (ct-by-type ct)))))]
                                               (second (sorted-clusters ci))))]]
                         [(:id a) cluster])]
    [(vec clusters) actor-clusters]))

(defn make-clusters2 [actors clusters actor-clusters]
  (let [actors (vec (map-indexed #(assoc %2 :id %1) actors))]
    (println (count actors) (count clusters) (count (filter #(> (count actors) (first %)) (take 100 actor-clusters))))
    (reduce #(vector (update-in (first %1) [(first %2) :clusters] conj (second %2))
                     (update-in (second %1) [(second %2) :actors] conj (first %2)))
            [actors clusters]
            actor-clusters)))

(defn actor->day [k]
  (case k
    :contract-day :contractions
    :illness-day :illnesses
    :death-day :deaths
    :recovery-day :recoveries
    :hospitalization-day :hospitalizations
    :discharge-day :discharges
    nil))

(defn run-simulation [[actors clusters] n cluster-type-transmission-by-cases]
  (let [i (repeatedly n #(rand-int (count actors)))]
    (loop [actors (reduce #(update %1 %2 assoc :contract-day 0, :illness-day 5, :recovery-day 20, :source -1) actors i)
           contagious {10 (vec i)}
           day 1
           max-day 20
           day-counts {0 {:contractions n}, 5 {:illnesses n}, 20 {:recoveries n}}
           total-counts {0 {:contractions n}}
           cttd cluster-type-transmission-by-cases
           policy-change-days []]
      (let [ctt (into {} (for [[k v] (last (first cttd))]
                           [k (if (zero? v)
                                [[0 1]]
                                (for [i (range 11)]
                                  [i (is/pdf-binomial i :size 10 :prob v)]))]))
            infections (apply merge (for [i (mapcat contagious (range day (+ 7 day)))
                                          :let [a (actors i)]
                                          ;; You can only transmit if you're contagious,
                                          ;; which happens 2 days before illness to 5 days after.
                                          :when (<= (- (get a :illness-day 1e6) 2)
                                                    day
                                                    (+ 5 (get a :illness-day 1e6)))
                                          cluster (map clusters (:clusters a))
                                          ;; In order to transmit you mustn't be symptomatic yet, or
                                          ;; the severity is low enough that you still go out, or
                                          ;; we're considering the household, who can still
                                          ;; get it even when you don't go out.
                                          :when (or (< day (get a :illness-day 1e6))
                                                    (= :household (:type cluster))
                                                    (< isolation-severity (:severity a)))
                                          :let [cluster-actors (vec (:actors cluster))]
                                          j (repeatedly (draw (ctt (:type cluster))) #(rand-int (count cluster-actors)))
                                          ;j (into #{} (repeatedly 10 #(rand-int (count cluster-actors))))
                                          ;:when (< (rand) ((last (first cttd)) (:type cluster)))
                                          :let [actor-id (cluster-actors j)]
                                          ;; Finally, the other actor you're transmitting to must not have
                                          ;; already contracted it, and they must be randomly unlucky enough
                                          ;; to be exposed based upon the transmission rate for the location.
                                          :when (and (< day (get-in actors [actor-id :contract-day] 1e6)))]
                                      (let [severity (:severity a)  ;; based upon age
                                            onset (int (+ 5 (* 13 (id/draw (id/beta-distribution 3 10)))))  ;; [2, 14] days of incubation, mean of 5
                                            ;; [7, 34] days of illness for most severe cases
                                            ;; [3, 15] days for the least severe still having symptoms
                                            recovery (if (< severity (- 1 hospitalization-rate)) (+ onset (int (* (max 3/7 severity) (+ 7.5 (* 28 (id/draw (id/beta-distribution 4 4))))))))
                                            hospitalization (if (nil? recovery) (+ onset 2 (int (* 13 (id/draw (id/beta-distribution 5 7))))))
                                            death (if (> severity (- 1 death-rate)) (+ hospitalization (int (+ 1.5 (* 22 (id/draw (id/beta-distribution 3 9)))))))
                                            discharge (if (and hospitalization (nil? death)) (+ hospitalization (int (+ 1.5 (* 42 (id/draw (id/beta-distribution 9 15)))))))
                                            terms (apply conj {}
                                                         [:contract-day day]
                                                         [:source (:id a)]
                                                         [:source-cluster (:id cluster)]
                                                         [:illness-day (+ day onset)]
                                                         (cond
                                                           death [[:hospitalization-day (+ day hospitalization)] [:death-day (+ day death)]]
                                                           discharge [[:hospitalization-day (+ day hospitalization)] [:recovery-day (+ day discharge)] [:discharge-day (+ day discharge)]]
                                                           :default [[:recovery-day (+ day recovery)]]))]
                                        ;(println "day" day ":" (:id a) "->" member-id "at" (dissoc cluster :members))
                                        {actor-id terms})))
            actors (reduce #(update %1 (first %2) into (second %2)) actors infections)
            contagious (apply merge-with into contagious
                              (for [i (map first infections)
                                    :let [a (actors i)
                                          illness-day (:illness-day a)]]
                                {(+ 5 illness-day) [i]}))
            new-days (flatten (map (comp vals #(select-keys % [:death-day :recovery-day])) (vals infections)))
            max-day (reduce max max-day new-days)
            safe-inc #(inc (or % 0))
            day-counts (reduce #(if-let [k2 (actor->day (first %2))]
                                  (update-in %1 [(second %2) k2] safe-inc)
                                  %1) day-counts (mapcat val infections))
            total-counts (assoc total-counts day (merge-with + {:day 1, (keyword (str "policy-" (count policy-change-days) "-day")) 1} (total-counts (dec day)) (day-counts day)))
            policy-change ((first (first cttd)) day day-counts total-counts)]
        ;(println day ":" (count infections) "new cases," (total-counts day) "totals")
        (if (or (> day max-day) (and policy-change (nil? (next cttd))))
          [actors
           day-counts
           total-counts
           policy-change-days]
          (if @halt-flag
            nil
            (recur actors (dissoc contagious day) (inc day) max-day day-counts total-counts (if policy-change (do (println "Switching to" (second cttd)) (next cttd)) cttd) (if policy-change (conj policy-change-days day) policy-change-days))))))))

(def cobb-cluster-types [{:type :worship, :level :household, :multiplicity {0 2/3, 1 1/3},
                          :locality (id/beta-distribution 1 10),
                          :subtype {{:name :catholic, :count 5} 1/10,
                                    {:name :methodist, :count 20} 2/10,
                                    {:name :presbyterian, :count 20} 2/10,
                                    {:name :small-baptist, :count 30} 3/20,
                                    {:name :big-baptist, :count 4} 3/20,
                                    {:name :lutheran, :count 15} 1/10,
                                    {:name :orthodox, :count 3} 1/30,
                                    {:name :synagoge, :count 4} 4/90,
                                    {:name :mosque, :count 2} 2/90}}
                         {:type :grocers, :level :hh-adult, :multiplicity {1 8/10, 2 16/100, 3 4/100},
                          :locality (id/beta-distribution 1 10),
                          :subtype {{:name :publix, :count 14} 0.6, {:name :krogers, :count 10} 0.4}}
                         {:type :school, :level :hh-children, :multiplicity {1 13/20, 0 7/20},
                          :locality (id/beta-distribution 1 60)
                          :subtype {{:name :local, :count 120} 1}}
                         {:type :work, :level :individual,
                          :locality (id/beta-distribution 1 15)
                          :multiplicity-by-age {0 {0 1}, 1 {0 7/8, 1 1/8}, 2 {0 1/6, 1 9/12, 2 1/12},
                                                3 {0 1/50, 1 47/50, 2 2/50}, 4 {0 1/50, 1 48/50, 2 1/50},
                                                5 {0 4/50, 1 45/50, 2 1/50}, 6 {0 1/3, 1 2/3},
                                                7 {0 2/5, 1 3/5}, 8 {0 4/5, 1 1/5}, 9 {0 49/50, 1 1/50}},
                          :subtype (into {} (for [name (range 150)
                                                  :let [insts (inc (rand-int 15))]]
                                              [{:name (keyword (str "employer" name)), :count insts}
                                               (/ (inc name) (reduce + (range 151)))]))}
                         {:type :store, :level :individual,
                          :locality (id/beta-distribution 1 10),
                          :multiplicity-by-age {0 {0 1/2, 1 1/2},
                                                1 {0 1/3, 1 3/30, 2 5/30, 3 7/30, 4 3/30, 5 2/30},
                                                2 {0 1/6, 1 1/6, 2 1/6, 3 1/6, 4 1/6, 5 1/6},
                                                3 {0 1/5, 1 1/5, 2 1/5, 3 1/5, 4 1/10, 5 1/10},
                                                4 {0 1/5, 1 1/5, 2 1/5, 3 1/5, 4 1/5},
                                                5 {0 1/4, 1 1/4, 2 1/4, 3 1/4},
                                                6 {0 1/4, 1 1/4, 2 1/4, 3 1/4},
                                                7 {0 1/4, 1 1/4, 2 1/4, 3 1/4},
                                                8 {0 1/3, 1 1/3, 2 1/3},
                                                9 {0 2/3, 1 1/3}},
                          :subtype (into {} (for [name (range 30)]
                                              [{:name (keyword (str "store" name)), :count 5} 1/30]))}])

(def atl-cluster-types [{:type :worship, :level :household, :multiplicity {0 2/3, 1 1/3},
                         :locality (id/beta-distribution 1 10),
                         :subtype {{:name :catholic, :count 30} 1/10,
                                   {:name :methodist, :count 120} 2/10,
                                   {:name :presbyterian, :count 120} 2/10,
                                   {:name :small-baptist, :count 180} 3/20,
                                   {:name :big-baptist, :count 24} 3/20,
                                   {:name :lutheran, :count 90} 1/10,
                                   {:name :orthodox, :count 18} 1/30,
                                   {:name :synagoge, :count 24} 4/90,
                                   {:name :mosque, :count 12} 2/90}}
                        {:type :grocers, :level :hh-adult, :multiplicity {1 8/10, 2 16/100, 3 4/100},
                         :locality (id/beta-distribution 1 10),
                         :subtype {{:name :publix, :count 84} 0.6, {:name :krogers, :count 60} 0.4}}
                        {:type :school, :level :hh-children, :multiplicity {1 13/20, 0 7/20},
                         :locality (id/beta-distribution 1 60)
                         :subtype {{:name :local, :count 720} 1}}
                        {:type :work, :level :individual,
                         :locality (id/beta-distribution 1 15)
                         :multiplicity-by-age {0 {0 1}, 1 {0 7/8, 1 1/8}, 2 {0 1/6, 1 9/12, 2 1/12},
                                               3 {0 1/50, 1 47/50, 2 2/50}, 4 {0 1/50, 1 48/50, 2 1/50},
                                               5 {0 4/50, 1 45/50, 2 1/50}, 6 {0 1/3, 1 2/3},
                                               7 {0 2/5, 1 3/5}, 8 {0 4/5, 1 1/5}, 9 {0 49/50, 1 1/50}},
                         :subtype (into {} (for [name (range 300)
                                                 :let [insts (inc (rand-int 45))]]
                                             [{:name (keyword (str "employer" name)), :count insts}
                                              (/ (inc name) (reduce + (range 301)))]))}
                        {:type :store, :level :individual,
                         :locality (id/beta-distribution 1 10),
                         :multiplicity-by-age {0 {0 1/2, 1 1/2},
                                               1 {0 1/3, 1 3/30, 2 5/30, 3 7/30, 4 3/30, 5 2/30},
                                               2 {0 1/6, 1 1/6, 2 1/6, 3 1/6, 4 1/6, 5 1/6},
                                               3 {0 1/5, 1 1/5, 2 1/5, 3 1/5, 4 1/10, 5 1/10},
                                               4 {0 1/5, 1 1/5, 2 1/5, 3 1/5, 4 1/5},
                                               5 {0 1/4, 1 1/4, 2 1/4, 3 1/4},
                                               6 {0 1/4, 1 1/4, 2 1/4, 3 1/4},
                                               7 {0 1/4, 1 1/4, 2 1/4, 3 1/4},
                                               8 {0 1/3, 1 1/3, 2 1/3},
                                               9 {0 2/3, 1 1/3}},
                         :subtype (into {} (for [name (range 60)]
                                             [{:name (keyword (str "store" name)), :count 15} 1/30]))}])

(def hundred-k-cluster-types [{:type :worship, :level :household, :multiplicity {0 2/3, 1 1/3},
                          :locality (id/beta-distribution 1 10),
                          :subtype {{:name :catholic, :count 1} 4/30,
                                    {:name :methodist, :count 3} 2/9,
                                    {:name :presbyterian, :count 2} 2/10,
                                    {:name :small-baptist, :count 6} 6/20,
                                    {:name :lutheran, :count 1} 13/90}}
                         {:type :grocers, :level :hh-adult, :multiplicity {1 8/10, 2 16/100, 3 4/100},
                          :locality (id/beta-distribution 1 10),
                          :subtype {{:name :publix, :count 1} 0.6, {:name :krogers, :count 1} 0.4}}
                         {:type :school, :level :hh-children, :multiplicity {1 13/20, 0 7/20},
                          :locality (id/beta-distribution 1 60)
                          :subtype {{:name :local, :count 12} 1}}
                         {:type :work, :level :individual,
                          :locality (id/beta-distribution 1 15)
                          :multiplicity-by-age {0 {0 1}, 1 {0 7/8, 1 1/8}, 2 {0 1/6, 1 9/12, 2 1/12},
                                                3 {0 1/50, 1 47/50, 2 2/50}, 4 {0 1/50, 1 48/50, 2 1/50},
                                                5 {0 4/50, 1 45/50, 2 1/50}, 6 {0 1/3, 1 2/3},
                                                7 {0 2/5, 1 3/5}, 8 {0 4/5, 1 1/5}, 9 {0 49/50, 1 1/50}},
                          :subtype (into {} (for [name (range 30)
                                                  :let [insts (id/draw [1 1 1 1 1 1 2 2 3])]]
                                              [{:name (keyword (str "employer" name)), :count insts}
                                               (/ (inc name) (reduce + (range 31)))]))}
                         {:type :store, :level :individual,
                          :locality (id/beta-distribution 1 10),
                          :multiplicity-by-age {0 {0 1/2, 1 1/2},
                                                1 {0 1/3, 1 3/30, 2 5/30, 3 7/30, 4 3/30, 5 2/30},
                                                2 {0 1/6, 1 1/6, 2 1/6, 3 1/6, 4 1/6, 5 1/6},
                                                3 {0 1/5, 1 1/5, 2 1/5, 3 1/5, 4 1/10, 5 1/10},
                                                4 {0 1/5, 1 1/5, 2 1/5, 3 1/5, 4 1/5},
                                                5 {0 1/4, 1 1/4, 2 1/4, 3 1/4},
                                                6 {0 1/4, 1 1/4, 2 1/4, 3 1/4},
                                                7 {0 1/4, 1 1/4, 2 1/4, 3 1/4},
                                                8 {0 1/3, 1 1/3, 2 1/3},
                                                9 {0 2/3, 1 1/3}},
                          :subtype (into {} (for [name (range 30)]
                                              [{:name (keyword (str "store" name)), :count (id/draw [1 1 1 1 1 2])} 1/30]))}])

(def lvl0 {:worship 0.005, :grocers 0.005, :work 0.03, :household 0.06, :store 0.0015, :school 0.05})
(def lvl1 {:worship 0.005, :grocers 0.005, :work 0.02, :household 0.07, :store 0.001, :school 0})
(defn lvl0_5 [x]
  {:worship (* 0.005 x) :grocers (* 0.005 x) :work (* 0.02 x) :household 0.07 :store (* 0.001 x) :school 0})
(def lvl2 {:worship 0.002, :grocers 0.0025, :work 0.005, :household 0.07, :store 0.0003, :school 0})
(def lvl3 {:worship 0.00125, :grocers 0.00125, :work 0.005, :household 0.08, :store 0.000025, :school 0})
(defn fuzz [m mean sd]
  (kvmap identity #(* % (Math/exp (id/draw (id/normal-distribution mean sd)))) m))

(defn plot-sim [[actors data _ policy-change-days]]
  (let [p (ic/xy-plot)
        max-days (inc (apply max (keys data)))
        sorted-data (sort data)
        totals (into {} (for [lbl [:contractions :illnesses :recoveries :deaths :hospitalizations]]
                          [lbl (vec (reductions + 0 (map #(get-in data [% lbl] 0) (range max-days))))]))
        contagious (drop 2
                     (reductions +
                        0 (map - (concat (map #(get % :illnesses 0) (map data (range max-days))) (repeat 7 0))
                              (concat (repeat 7 0) (map #(get % :illnesses 0) (map data (range max-days)))))))
        hospitalizations (reductions +
                           0 (map #(- %1 %2)
                                (map #(get-in data [% :hospitalizations] 0) (range max-days))
                                (map #(+ (get-in data [% :discharges] 0)
                                         (get-in data [% :deaths] 0)) (range max-days))))]
    (ic/set-stroke p :width 3)
    ;; Add the cumulative lines
    (doseq [lbl [:contractions :illnesses :recoveries :deaths :hospitalizations]]
      (ic/add-lines p (range max-days) (lbl totals)))
    ;; Add the healthy line
    ;(ic/add-lines p (range max-days) (map #(apply - (count actors) 0 (map (fn [a] (get-in data [a :contractions] 0)) (range %1))) (range max-days)))
    (ic/add-lines p [] [])
    ;; Add the transmissive cases
    (ic/add-lines p (range max-days) contagious)
    ;; Add the hospital load
    (ic/add-lines p (range max-days) hospitalizations)
    (doseq [[ds c] (map vector (range 1 9) [Color/orange Color/red Color/green Color/black Color/cyan Color/pink Color/magenta Color/blue])]
      (ic/set-stroke-color p c :dataset ds)
      (ic/set-stroke p :width 3 :dataset ds))
    (doseq [[ds pc c] (map vector (range 9 1000) policy-change-days (cycle [Color/cyan Color/yellow Color/white]))]
      (ic/add-lines p [(inc pc) (inc pc)] [0 (* 1.2 (get-in totals [:illnesses max-days] 0))])
      ;(ic/set-stroke-color p c :dataset ds)
      ;(ic/set-stroke p :width 1 :dataset ds)
      )
    (i/view p)
    p))

(defn plot-sims [sims & [alignments]]
  (let [p (ic/xy-plot)
        sims&alignments (map vector (range) sims (or alignments (repeat (count sims) 0)))]
    (ic/set-alpha p (/ (Math/pow (count sims) 0.5)))
    (ic/set-stroke p :width 3)
    (doseq [[j [actors data] offset] sims&alignments]
      (let [offset (or offset 0)
            max-days (inc (apply max (keys data)))
            days (range (- offset) (- max-days offset))
            sorted-data (sort data)
            totals (into {} (for [lbl [:contractions :illnesses :recoveries :deaths :hospitalizations]]
                              [lbl (vec (reductions + 0 (map #(get-in data [% lbl] 0) (range max-days))))]))
            contagious (drop 2
                             (reductions +
                                         0 (map - (concat (map #(get % :illnesses 0) (map data (range max-days))) (repeat 7 0))
                                                (concat (repeat 7 0) (map #(get % :illnesses 0) (map data (range max-days)))))))
            hospitalizations (reductions +
                                         0 (map #(- %1 %2)
                                                (map #(get-in data [% :hospitalizations] 0) (range max-days))
                                                (map #(+ (get-in data [% :discharges] 0)
                                                         (get-in data [% :deaths] 0)) (range max-days))))]
        ;; Add the cumulative lines
        (doseq [[lbl i c] [[:contractions 1 Color/orange] [:illnesses 2 Color/red]
                           [:recoveries 3 Color/green] [:deaths 4 Color/black]]]
          (ic/add-lines p days (lbl totals))
          (ic/set-stroke-color p c :dataset (+ i (* j 8)))
          )
        ;; Add the healthy line
        (ic/add-lines p days (map #(apply - (count actors) 0 (map (fn [a] (get-in data [a :contractions] 0)) (range %1))) (range max-days)))
        (ic/set-stroke-color p Color/white :dataset (+ 5 (* j 8)))
        ;; Add the transmissive cases
        (ic/add-lines p days contagious)
        (ic/set-stroke-color p Color/magenta :dataset (+ 6 (* j 8)))
        ;; Add the hospital load
        (ic/add-lines p days (:hospitalizations totals))
        (ic/set-stroke-color p Color/cyan :dataset (+ 7 (* j 8)))
        (ic/add-lines p days hospitalizations)
        (ic/set-stroke-color p Color/blue :dataset (+ 8 (* j 8)))
        ))
    (i/view p)
    p))

(defn network-degree [actors clusters]
  (let [i (rand-int (count actors))]
    (loop [s #{i}
           n #{i}
           c [1]]
      (if (empty? n)
        c
        (let [cis (into #{} (for [a (map actors n)
                                 ci (:clusters a)]
                             ci))
              pn (into #{} (for [c (map clusters cis)                                 
                                 a2 (:actors c)]
                             a2))
              nn (set/difference pn s)]
          (println (count s) (count pn) (count nn) c)
          (Thread/sleep 100)
          (recur (into s nn) nn (conj c (count nn))))))))

(defn calc-r [[actors] days]
  (let [days (if (number? days) #{days} (into #{} days))
        infected (into #{} (map :id (filter #(days (get % :contract-day 1e7)) actors)))
        spreads (frequencies (vals (frequencies (filter infected (map :source actors)))))
        num (float (reduce + (map (partial apply *) spreads)))
        denom (count infected)                    ;(float (reduce + (vals spreads)))
        ]
    (/ num denom)))

(defn calc-r0 [[actors data _ policy-changes]]
  (let [data-days (map second (sort data))
        totals (reductions + (map #(get % :contractions 0) data-days))
        total (last totals)
        tenth-day (last (for [[day t] (map vector (range) totals)
                              :when (and (<= t (/ (count actors) 10))
                                         (< day (get policy-changes 0 1e8)))]
                           day))]
    (calc-r [actors] (range (inc tenth-day)))))

(defn calc-doubling [[_ _ totals] days & [kw]]
  (let [days (if (number? days) #{days} (into #{} days))
        kw (or kw :contractions)
        min-day (apply min days)
        max-day (apply max days)
        min-val (get-in totals [min-day kw] 0)
        max-val (get-in totals [max-day kw] 0)]
    (println min-day max-day min-val max-val (float (/ max-val min-val)))
    (/ (- max-day min-day)
       (/ (Math/log10 (/ max-val min-val))
          (Math/log10 2)))))

(defn summarize [[actors data totals policy-change-days]]
  (let [eradication-days (apply max (keys data))
        total-infected (get-in totals [eradication-days :contractions] 0) #_(reduce + (map #(get % :contractions 0) (vals data)))
        sorted-data (sort data)
        peak-illnesses (reduce #(if (>= (second %1) (second %2)) %1 %2)
                               (->> eradication-days
                                    inc
                                    range
                                    (map totals)
                                    (map #(- (get % :illnesses 0) (get % :recoveries 0) (get % :deaths 0)))
                                    (map-indexed vector))
                               #_(map vector (map first sorted-data) (reductions 
                                                        #(+ %1 (- (get %2 :illnesses 0) (get %2 :recoveries 0)))
                                                        0 (map second sorted-data))))
        peak-recoveries (reduce #(if (>= (second %1) (second %2)) %1 %2)
                               (->> eradication-days
                                    inc
                                    range
                                    (map data)
                                    (map #(get % :recoveries 0))
                                    (map-indexed vector))
                               #_(map vector (keys data) (map #(- (get % :recoveries 0) (get % :illnesses 0)) (vals data))))
        total-deaths (-> eradication-days totals :deaths) #_(reduce + (map #(get % :deaths 0) (vals data)))
        peak-hospitalizations (reduce #(if (>= (second %1) (second %2)) %1 %2)
                               (->> eradication-days
                                    inc
                                    range
                                    (map totals)
                                    (map #(- (get % :hospitalizations 0) (get % :discharges 0) (get % :deaths 0)))
                                    (map-indexed vector))
                               #_(map vector (map first sorted-data)
                                           (reductions
                                            #(+ %1 (- (get %2 :hospitalizations 0) (+ (get %2 :discharges 0)
                                                                                      (get %2 :deaths 0))))
                                            0 (map second sorted-data))))]
    {:eradication-days eradication-days,
     :total-infected total-infected,
     :peak-illnesses peak-illnesses,
     :peak-recoveries peak-recoveries,
     :r0 (calc-r0 [actors data]),
     :policy-changes policy-change-days
     :total-deaths total-deaths
     :peak-hospitalizations peak-hospitalizations}))

(def ga-hospitalizations [394 473 566 617 666 707 833 952 1056 1158 1239 1283 1332 1774 1993])
