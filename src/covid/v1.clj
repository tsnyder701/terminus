(ns covid.v1
  (:require [incanter.core :as i]
            [incanter.charts :as ic]
            [incanter.distributions :as id]
            [clojure.set :as set]))

(def isolation-severity 0.3)

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
  (reduce #(if (< %1 (second %2))
             (reduced (first %2))
             (- %1 (second %2)))
          (rand)
          m))

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
                           {:id (+ i j), :loc [x y], :age age, :sex sex, :severity severity,
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
                           {:id (+ i (count hh-adults) j), :loc [x y], :age age, :sex sex,
                            :severity severity, :cluster-names cts}))))))))

(defn round-location [[x y] d]
  [(/ (int (* x d)) d) (/ (int (* y d)) d)])

(defn index-locations [objects d]
  (reduce #(update %1 (round-location (:loc %2) d) conj %2) {} objects))

(defn dist [[x1 y1] [x2 y2]]
  (+ (Math/abs (- x1 x2)) (Math/abs (- y1 y2))))

(defn make-clusters [actors cluster-types]
  (let [ckpt 1
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
                         [(:id a) cluster])
        ckpt (do (println "mc" ckpt) (inc ckpt))
        ac-by-actor (kvmap identity #(mapv second %) (group-by first actor-clusters))
        ac-by-cluster (kvmap identity #(mapv first %) (group-by second actor-clusters))
        ckpt (do (println "mc" ckpt) (inc ckpt))
        actors (reduce #(assoc-in %1 [(first %2) :clusters] (second %2)) actors ac-by-actor)
        ckpt (do (println "mc" ckpt) (inc ckpt))
        clusters (reduce #(assoc-in %1 [(first %2) :actors] (second %2)) clusters ac-by-cluster)]
    [actors clusters cluster-types]))

(defn run-simulation [[actors clusters] n cluster-type-transmission-by-cases]
  (let [i (repeatedly n #(rand-int (count actors)))]
    (loop [actors (reduce #(update %1 %2 assoc :contract-day 0, :illness-day 5, :recovery-day 20, :source -1) actors i)
           contracted {10 (vec i)}
           day 1
           max-day 20
           cumulative-ill {0 0, 1 0, 2 0, 3 0, 4 0, 5 1}
           cttd cluster-type-transmission-by-cases]
      (let [infections (apply merge (for [[cd is] contracted
                                          i is
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
                                          :let [cluster-actors (:actors cluster)]
                                          j (into #{} (repeatedly 10 #(rand-int (count cluster-actors))))
                                          :when (< (rand) ((second (first cttd)) (:type cluster)))
                                          :let [actor-id (cluster-actors j)]
                                          ;; Finally, the other actor you're transmitting to must not have
                                          ;; already contracted it, and they must be randomly unlucky enough
                                          ;; to be exposed based upon the transmission rate for the location.
                                          :when (and (< day (get-in actors [actor-id :contract-day] 1e6)))]
                                      (let [severity (:severity a)  ;; based upon age
                                            incubation (rand-int 10)  ;; [0, 9] days of incubation
                                            ;; [7, 34] days of illness for most severe cases
                                            ;; [1, 7] days for the least severe still having symptoms
                                            illness (int (* (max 0.2 severity) (+ 7 (rand-int 28)))) 
                                            terms (conj {}
                                                        [:contract-day day]
                                                        [:source (:id a)]
                                                        [:source-cluster (:id cluster)]
                                                        [:illness-day (+ day incubation)]
                                                        ;; 2% of cases result in death
                                                        (if (< 0.98 severity)
                                                          [:death-day (+ day incubation illness)]
                                                          [:recovery-day (+ day incubation illness)]))]
                                        #_(println "day" day ":" (:id a) "->" member-id "at" (dissoc cluster :members))
                                        {actor-id terms})))
            actors (reduce #(update %1 (first %2) into (second %2)) actors infections)
            contracted (apply merge-with into contracted
                              (for [i (map first infections)
                                    :let [a (actors i)
                                          illness-day (:illness-day a)]]
                                {(+ 5 illness-day) [i]}))
            new-days (flatten (map (comp vals #(select-keys % [:death-day :recovery-day])) (vals infections)))
            max-day (reduce max max-day new-days)
            safe-inc #(inc (or % 0))
            cumulative-ill (reduce #(update %1 (:illness-day %2) safe-inc) cumulative-ill (vals infections))
            day-ill (reduce + (map second (filter #(<= (first %) day) cumulative-ill)))]
        #_(println day ":" (count infections) "new cases," (reduce + (vals cumulative-ill)) "total ill")
        (if (> day max-day)
          [actors
           (->> (for [a actors
                      [k v] a]
                  (case k
                    :contract-day [v :contractions]
                    :illness-day [v :illnesses]
                    :death-day [v :deaths]
                    :recovery-day [v :recoveries]
                    nil))
                (filter identity)
                (group-by first)
                (map #(vector (first %1) (frequencies (map second (second %1)))))
                (into {}))]
          (recur actors (dissoc contracted day) (inc day) max-day cumulative-ill (if (> day-ill (first (first cttd))) (do #_(println "After" day-ill "vs." (first (first cttd)) "Switching to" (second (second cttd))) (next cttd)) cttd)))))))

(def cluster-types [{:type :worship, :level :household, :multiplicity {0 2/3, 1 1/3},
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

(defn plot-sim [[actors data]]
  (let [p (ic/xy-plot)
        max-days (inc (apply max (keys data)))
        sorted-data (sort data)
        totals (into {} (for [lbl [:contractions :illnesses :recoveries :deaths]]
                          [lbl (vec (reductions + 0 (map (comp #(get % lbl 0) second) sorted-data)))]))
        contagious (drop 1
                     (reductions + 
                       (map - (concat (map #(get % :illnesses 0) (map second sorted-data)) (repeat 7 0))
                              (concat (repeat 7 0) (map #(get % :illnesses 0) (map second sorted-data))))))
        hospitalizations (reductions +
                           (map #(* 0.2 (- %1 %2))
                                (map #(get (second %) :illnesses 0) sorted-data)
                                (map #(+ (get (second %) :recoveries 0)
                                         (get (second %) :deaths 0)) sorted-data)))]
    ;; Add the cumulative lines
    (doseq [lbl [:contractions :illnesses :recoveries :deaths]]
      (ic/add-lines p (range max-days) (lbl totals)))
    ;; Add the healthy line
    (ic/add-lines p (range max-days) (map #(apply - (count actors) 0 (map (fn [a] (get-in data [a :contractions] 0)) (range %1))) (range max-days)))
    ;; Add the transmissive cases
    (ic/add-lines p (range max-days) contagious)
    ;; Add the hospital load
    (ic/add-lines p (range max-days) hospitalizations)
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
        denom (float (reduce + (vals spreads)))]
    (/ num denom)))

(defn calc-r0 [[actors data]]
  (let [data-days (map second (sort data))
        totals (reductions + (map #(get % :contractions 0) data-days))
        total (last totals)
        tenth-day (first (for [[day t] (map vector (range) totals)
                               :when (>= t (/ total 10))]
                           day))]
    (calc-r [actors] tenth-day)))

(defn summarize [[actors data]]
  (let [eradication-days (apply max (keys data))
        total-infected (reduce + (map #(get % :contractions 0) (vals data)))
        sorted-data (sort data)
        peak-illnesses (reduce #(if (>= (second %1) (second %2)) %1 %2)
                               (map vector (map first sorted-data) (reductions 
                                                        #(+ %1 (- (get %2 :illnesses 0) (get %2 :recoveries 0)))
                                                        0 (map second sorted-data))))
        peak-recoveries (reduce #(if (>= (second %1) (second %2)) %1 %2)
                                (map vector (keys data) (map #(- (get % :recoveries 0) (get % :illnesses 0)) (vals data))))]
    {:eradication-days eradication-days,
     :total-infected total-infected,
     :peak-illnesses peak-illnesses,
     :peak-recoveries peak-recoveries,
     :r0 (calc-r0 [actors data])}))
