(ns covid.v2
  (:require [incanter.core :as i]
            [incanter.charts :as ic]
            [incanter.distributions :as id]
            [incanter.io :as iio]
            [incanter.stats :as is]
            [incanter.svg :as isvg]
            [incanter.pdf :as ipdf]
            [clojure.set :as set])
  (:import [java.awt Color]))

(declare atl-hospitalizations avg summarize avg-sims)

;; The severity of illness, above which, an actor doesn't go outside their household after :illness-day
(def isolation-severity 0.3)
;; The severity, above which, an actor will eventually die if they contract COVID
;; To convert to a percentile, you must first weight by age demographics
(def death-severity 0.96)
;; The severity, above which, an actor will eventually go to the hospital if they contract COVID
;; To convert to a percentile, you must first weight by age demographics
(def hospitalization-severity 0.8694)

(def halt-flag (atom false))

(def atl-isolation-severity 0.3)
(def atl-hospitalization-severity 0.885)
(def atl-death-severity 0.975)

(def chi-isolation-severity 0.3)
(def chi-hospitalization-severity 0.96)
(def chi-death-severity 0.8694)

;; kvmap transforms a map by applying kf to each key and vf to each value
;; kf should be one-to-one or the output is undefined
(defn kvmap [kf vf m]
  (into {} (for [[k v] m]
             [(kf k) (vf v)])))

;; normalize takes a map of keys to relative proprotions and returns a map
;; of keys to probabilities, suitable for use with draw
(defn normalize [m]
  (let [s (reduce + (vals m))]
    (kvmap identity #(/ %1 s) m)))

;; Racial groups used within this simulation.
(def races #{:white :black :amerindian :asian :polynesian :other})
;; Ethnic specifiers used within this simulation.
(def ethnicities #{:latino})

;; Racial composition of places.
(def chicago-race-demo {:latino 0.198, :white 0.328, :black 0.297, :amerindian 0.003, :asian 0.064, :polynesian 0.001, :other 0.109})

;; Scale factor for severity determined by race in places.
(def chicago-sex-severity {:male 8/7, :female 7/8})
(def chicago-age-severity {0 1/3, 1 1/2, 2 10/19, 3 100/165, 4 10/13, 5 100/111, 6 100/92, 7 100/65, 8 100/54, 9 2})
(def chicago-race-severity {:latino 1.05, :white 1.075, :black 1.7, :amerindian 1, :asian 1.2, :polynesian 1, :other 0.3})

;; The relative numbers of people in each decade of life in the US, according to 2010 Census
(def age-demo (normalize {0 40, 1 42, 2 43, 3 41, 4 41, 5 42, 6 36, 7 20, 8 8, 9 1}))
;; Beta distribution parameters to use for drawing the severity of disease for each age cohort
;; The values were chosen such that the distribution mean matched death rates for each age cohort according
;; to a paper I found
;; TODO(tsnyder): Find the paper and link it here
(def age-severity {0 [10/19 19/10], 1 [5/8 8/5], 2 [50/73 73/50], 3 [3/4 4/3], 4 [25/32 32/25], 5 [15/16 16/15], 6 [9/8 8/9], 7 [11/8 8/11], 8 [7/4 4/7], 9 [8/4 4/8]})
;; Beta distribution parameters to use for drawing the severity of disease for each age&sex cohort
;; The values are the age-severity values, but scaled by the reported sex difference observed in China
;; TODOO(tsnyderr): Find the paper and link it here
(def age-sex-severity (kvmap identity (partial apply id/beta-distribution)
                             (for [[age [a b]] age-severity
                                   [sex scale] [[:male 1.2] [:female 0.8]]]
                               [[age sex] [(* a scale) (/ b scale)]])))
;; Distribution of number of children per household that has children
(def household-children (normalize {1 14081, 2 12853, 3 4500, 4 2000, 5 400, 6 100}))
;; Distribution of household size
(def household-size (normalize {1 28, 2 34, 3 15, 4 13, 5 6, 6 2, 7 1, 8 0.2}))
;; Distribution of household compositions
;; Each element in the set maps to an identity below and are defined as follows:
;;   mother - An adult female in a household with children
;;   father - An adult male in a household with children
;;   man - An adult male in a household without children
;;   woman - An adult female in a household without children
;;   parent - The parent (who is not the head of household) of adult man or woman (who is head of household)
;;   other - An unrelated, non-coupled adult (i.e. roommate)
;;   children - One or more children whose guardian is head of household
(def households (normalize {#{:mother :father :children} 20, #{:man :woman} 28,
                            #{:mother :children} 7, #{:woman :parent} 6,
                            #{:father :children} 2, #{:man :parent} 2,
                            #{:man} 12, #{:man :other} 4,
                            #{:woman} 15, #{:woman :other} 3}))
;; Distributions of age by identity
(def identity-ages {:mother (normalize {2 20, 3 35, 4 35, 5 30, 6 5, 7 1}),
                    :father (normalize {2 15, 3 38, 4 38, 5 35, 6 10, 7 2}),
                    :man (normalize {1 5, 2 30, 3 34, 4 30, 5 25, 6 20, 7 10, 8 4, 9 1}),
                    :woman (normalize {1 3, 2 30, 3 34, 4 30, 5 25, 6 22, 7 12 8 5, 9 2}),
                    :parent (normalize {4 10, 5 20, 6 30, 7 30, 8 20, 9 5})
                    :children (normalize {0 50, 1 40})
                    :other (normalize {2 43, 3 41, 4 41, 5 42, 6 36, 7 20, 8 8, 9 1})})
;; Distribution of sex by identity
(def identity-sexes {:mother {:female 1},
                     :father {:male 1},
                     :man {:male 1},
                     :woman {:female 1},
                     :parent {:male 1/2, :female 1/2},
                     :children {:male 1/2, :female 1/2},
                     :other {:male 3/4, :female 1/4}})

;; The draw function takes a sequence of key-value pairs, returning a key with probability value provided
;; the sum of values equals 1.
(defn draw [m]
  (or (reduce #(if (< %1 (second %2))
                 (reduced (first %2))
                 (- %1 (second %2)))
              (rand)
              m)
      (first (last m))))

;; make-actors creates n actors in a virtual city
;; Each actor belongs to a household, defined by :loc, chosen from a 2D normal distribution
;; Each actor engages in a number of cluster types, as determined by cluster-types
;; Household composition and actor ages are determined by demographic data defined above
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

;; round-location bins the location into one of d*d bins
(defn round-location [[x y] d]
  [(/ (int (* x d)) d) (/ (int (* y d)) d)])

;; index-locations bins the locations of objects
(defn index-locations [objects d]
  (reduce #(update %1 (round-location (:loc %2) d) conj %2) {} objects))

(defn abs [x]
  (if (neg? x)
    (- x)
    x))

;; dist finds the L-1 distance (Manhatten block distance) between two locations
(defn dist [[x1 y1] [x2 y2]]
  (+ (abs (- x1 x2)) (abs (- y1 y2))))

;; make-clusters is deprecated in favor of make-clusters2
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

;; make-actor-clusters creates clusters and pairings between actors and clusters
;; clusters are instances of cluster type & subtype, as defined by cluster-types
;; actors are assigned to clusters matching their type & subtype, and prefer
;; instances that are closer to them based upon the cluster type locality preference
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

;; make-clusters2 updates actors and clusters based upon the associations in actor-clusters
(defn make-clusters2 [actors clusters actor-clusters]
  (let [actors (vec (map-indexed #(assoc %2 :id %1) actors))]
    (println (count actors) (count clusters) (count (filter #(> (count actors) (first %)) (take 100 actor-clusters))))
    (reduce #(vector (update-in (first %1) [(first %2) :clusters] conj (second %2))
                     (update-in (second %1) [(second %2) :actors] conj (first %2)))
            [actors clusters]
            actor-clusters)))

;; actor->day maps an actor's day key to a day's aggregate key
(defn actor->day [k]
  (case k
    :contract-day :contractions
    :illness-day :illnesses
    :death-day :deaths
    :recovery-day :recoveries
    :hospitalization-day :hospitalizations
    :discharge-day :discharges
    nil))

;; run-simulation runs the COVID transmission simulation until all no actor has the illness
;; it starts by infecting n actors on day 0
;; cluster-type-transmission-by-cases is sequence of [fn {}] pairs, where the function must
;; accept the current day, the day-counts map, and the day-totals map; and the map indicates
;; the level of spreading for the given cluster type; once the fn returns true, the next element
;; becomes the active policy for the next day.
;; The function returns the actors, updated with their day of contraction, illness, hospitalization, discharge, recovery, and/or death; the day-counts; the day-totals; and the days after which the policy, defined by
;; cluster-type-transmission-by-cases, was changed.
(defn run-simulation [[actors clusters] n cluster-type-transmission-by-cases & {:keys [verbosity isolation-severity hospitalization-severity death-severity] :or {verbosity 0, isolation-severity isolation-severity, hospitalization-severity hospitalization-severity, death-severity death-severity}}]
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
                                      (let [severity (:severity (actors actor-id))  ;; based upon age
                                            onset (int (+ 2 (* 13 (id/draw (id/beta-distribution 3 10)))))  ;; [2, 14] days of incubation, mean of 5
                                            hospitalization (if (< hospitalization-severity severity) (+ onset 2 (int (* 13 (id/draw (id/beta-distribution 2 3))))))
                                            death (if (> severity death-severity) (+ hospitalization (int (+ 1.5 (* 10 (id/draw (id/beta-distribution 1 2)))))))
                                            discharge (if (and hospitalization (nil? death)) (+ hospitalization (int (+ 1.5 (* 10 (id/draw (id/beta-distribution 1 2)))))))
                                            recovery (+ onset (int (* (max 3/7 severity) (+ 7.5 (* 28 (id/draw (id/beta-distribution 4 4)))))))
                                            terms (apply conj {}
                                                         [:contract-day day]
                                                         [:source (:id a)]
                                                         [:source-cluster (:id cluster)]
                                                         [:illness-day (+ day onset)]
                                                         (cond
                                                           death [[:hospitalization-day (+ day hospitalization)] [:death-day (+ day death)]]
                                                           discharge [[:hospitalization-day (+ day hospitalization)] [:recovery-day (+ day (max recovery discharge))] [:discharge-day (+ day discharge)]]
                                                           :default [[:recovery-day (+ day recovery)]]))]
                                        (if (<= 3 verbosity) (println "day" day ":" (:id a) "->" actor-id "at" (dissoc cluster :actors)))
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
        (if (<= 2 verbosity) (println day ":" (count infections) "new cases," (total-counts day) "totals"))
        (if (or (> day max-day) (and policy-change (nil? (next cttd))))
          [actors
           day-counts
           total-counts
           policy-change-days]
          (if @halt-flag
            nil
            (recur actors (dissoc contagious day) (inc day) max-day day-counts total-counts (if policy-change (do (if (<= 1 verbosity) (println "Switching to" (second cttd))) (next cttd)) cttd) (if policy-change (conj policy-change-days day) policy-change-days))))))))

;; cluster type definition modeling Cobb County, GA with a population of 750,000.
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

;; cluster type modeling a city of 6M actors. Scaled up version of Cobb County.
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

;; cluster type modeling a city of 100,000. Scaled down version of Cobb County.
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

;; The following define the transmission rates for use within run-simulation.
;; lvl0 - Nominal transmission rates with no social distancing
;; lvl1 - Schools closed, some work moved to WFH, stores visited less frequently
;; lvl2 - Schools closed, most work closed or WFH, most worship services stopped, grocers institute extra cleaning, stores visited rarely
;; lvl3 - Schools closed, most work closed or WFH, nearly all worship services stopped, grocers institute additional protective policies, stores almost never visited
;; lvl0_5 - Schools closed, some work moved to WFH, most values scaled by x
(def lvl0 {:worship 0.005, :grocers 0.005, :work 0.03, :household 0.06, :store 0.0015, :school 0.05})
(def lvl1 {:worship 0.005, :grocers 0.005, :work 0.02, :household 0.07, :store 0.001, :school 0})
(defn lvl0_5 [x]
  {:worship (* 0.005 x) :grocers (* 0.005 x) :work (* 0.02 x) :household 0.07 :store (* 0.001 x) :school 0})
(def lvl1_5 {:worship 0.002, :grocers 0.003, :work 0.008, :household 0.07, :store 0.0005, :school 0})
(def lvl2 {:worship 0.002, :grocers 0.0025, :work 0.005, :household 0.07, :store 0.0003, :school 0})
(def lvl3 {:worship 0.00125, :grocers 0.00125, :work 0.005, :household 0.08, :store 0.000025, :school 0})
(def lvl4 {:worship 0.0, :grocers 0.0, :work 0.0, :household 0.0, :store 0.0, :school 0})
(defn fuzz [m mean sd]
  (kvmap identity #(* % (Math/exp (id/draw (id/normal-distribution mean sd)))) m))

(defn plot-line [p xs ys c w ds & [n dash]]
  (ic/add-lines p xs ys :series-label n)
  (ic/set-stroke-color p c :dataset ds)
  (apply ic/set-stroke p :width w :dataset ds (if dash [:dash dash])))

(defn plot-legend []
  (doto (ic/xy-plot [] [] :series-label "Exposures")
    (ic/set-stroke-color (Color. 1.0 0.7 0.0))
    (ic/set-stroke :width 5)
    (plot-line [] [] (Color. 1.0 0.0 0.0) 5 1 "Illnesses")
    (plot-line [] [] (Color. 0.0 1.0 0.0) 5 2 "Recoveries")
    (plot-line [] [] (Color. 0.3125 0.625 1.0) 5 3 "Hospitalizations")
    (plot-line [] [] (Color. 0.0 0.0 0.0) 5 4 "Deaths")))

(defn plot-legend-deaths []
  (doto (ic/xy-plot [] [] :series-label "Mean Predicted Deaths")
    (ic/set-stroke-color (Color. 0 0 0))
    (ic/set-stroke :width 5)
    (ic/add-lines [] [] :series-label "Simulation Deaths")
    (ic/set-stroke-color (Color. 0. 0. 0. 0.4) :dataset 1)
    (ic/set-stroke :width 3 :dataset 1)
    (ic/add-points [] [] :series-label "Observed Deaths")))

(defn plot-legend-hospitalizations []
  (doto (ic/xy-plot [] [] :series-label "Mean Hospital Census")
    (ic/set-stroke-color (Color. 0. 0. 1.))
    (ic/set-stroke :width 5)
    (ic/add-lines [] [] :series-label "Mean Hospitalizations")
    (ic/set-stroke-color (Color. 0. 0.5 0.5) :dataset 1)
    (ic/set-stroke :width 5 :dataset 1)
    (ic/add-points [] [] :series-label "Observed Hospitalizations")))

(defn plot-sim [[actors data _ policy-change-days]]
  (let [p (ic/xy-plot)
        max-days (inc (apply max (keys data)))
        sorted-data (sort data)
        totals (into {} (for [lbl [:contractions :illnesses :recoveries :deaths :hospitalizations]]
                          [lbl (vec (reductions + (map #(get-in data [% lbl] 0) (range max-days))))]))
        contagious (drop 2
                     (reductions +
                        (map - (concat (map #(get % :illnesses 0) (map data (range max-days))) (repeat 7 0))
                              (concat (repeat 7 0) (map #(get % :illnesses 0) (map data (range max-days)))))))
        hospitalizations (reductions +
                           (map #(- %1 %2)
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

(defn plot-compartments [[actors data _ policy-change-days] & [p j]]
  (let [max-days (inc (apply max (keys data)))
        sorted-data (sort data)
        totals (into {} (for [lbl [:contractions :illnesses :recoveries :deaths :hospitalizations]]
                          [lbl (vec (reductions + (map #(get-in data [% lbl] 0) (range max-days))))]))
        contagious (drop 2
                     (reductions +
                        (map - (concat (map #(get % :illnesses 0) (map data (range max-days))) (repeat 7 0))
                              (concat (repeat 7 0) (map #(get % :illnesses 0) (map data (range max-days)))))))
        hospitalizations (reductions +
                           (map #(- %1 %2)
                                (map #(get-in data [% :hospitalizations] 0) (range max-days))
                                (map #(+ (get-in data [% :discharges] 0)
                                         (get-in data [% :deaths] 0)) (range max-days))))
        p (if p
            (doto p (ic/add-lines (range max-days) (map #(- (count actors) %) (totals :contractions)) :series-label "Susceptible"))
            (ic/xy-plot (range max-days) (map #(- (count actors) %) (totals :contractions)) :legend true :series-label "Susceptible" :title "SEIRD" :subtitle "Counts by Day" :y-label "Population" :x-label "Simulation Days"))
        j (or j 0)]
    #_(ic/add-lines p (range max-days) (map #(- (count actors) %) (totals :contractions)) :series-label "Susceptible")
    (ic/add-lines p (range max-days) (map #(- %1 %2) (totals :contractions) (totals :illnesses)) :series-label "Exposed")
    (ic/add-lines p (range max-days) (map #(- %1 %2 %3) (totals :illnesses) (totals :recoveries) (totals :deaths)) :series-label "Infectious")
    (ic/add-lines p (range max-days) (totals :recoveries) :series-label "Recovered")
    (ic/add-lines p (range max-days) (totals :deaths) :series-label "Dead")
    (doseq [[ds c] (map vector (range 0 5) [Color/green Color/orange Color/red Color/blue Color/black])]
      (ic/set-stroke-color p c :dataset (+ (* 5 j) ds))
      (ic/set-stroke p :width 1 :dataset (+ (* 5 j) ds)))
    (i/view p)
    p))

(defn plot-sims [sims & [alignments title x-axis]]
  (let [p (ic/xy-plot [] [] :title title :x-label x-axis :y-label "Population")
        sims&alignments (map vector (range) sims (or alignments (repeat (count sims) 0)))
        alpha (float (/ (Math/pow (count sims) 0.75)))]
    (doseq [[j [actors data] offset] sims&alignments]
      (let [offset (or offset 0)
            max-days (inc (apply max (keys data)))
            days (range (- offset) (- max-days offset))
            sorted-data (sort data)
            totals (into {} (for [lbl [:contractions :illnesses :recoveries :deaths :hospitalizations]]
                              [lbl (vec (reductions + (map #(get-in data [% lbl] 0) (range max-days))))]))
            contagious (drop 2
                             (reductions +
                                         (map - (concat (map #(get % :illnesses 0) (map data (range max-days))) (repeat 7 0))
                                                (concat (repeat 7 0) (map #(get % :illnesses 0) (map data (range max-days)))))))
            hospitalizations (reductions +
                                         (map #(- %1 %2)
                                                (map #(get-in data [% :hospitalizations] 0) (range max-days))
                                                (map #(+ (get-in data [% :discharges] 0)
                                                         (get-in data [% :deaths] 0)) (range max-days))))]
        ;; Add the cumulative lines
        (doseq [[lbl i c] [[:contractions 1 (Color. 1.0 0.7 0.0 alpha)]
                           [:illnesses 2 (Color. 1.0 0.0 0.0 alpha)]
                           [:recoveries 3 (Color. 0.0 1.0 0.0 alpha)]
                           [:deaths 4 (Color. 0.25 0.25 0.25 alpha)]]]
          (ic/add-lines p days (lbl totals))
          (ic/set-stroke-color p c :dataset (+ i (* j 8)))
          )
        ;; Add the healthy line
        (ic/add-lines p days [] #_(map #(apply - (count actors) 0 (map (fn [a] (get-in data [a :contractions] 0)) (range %1))) (range max-days)))
        (ic/set-stroke-color p (Color. 1.0 1.0 1.0 alpha) :dataset (+ 5 (* j 8)))
        ;; Add the transmissive cases
        (ic/add-lines p days [] #_contagious)
        (ic/set-stroke-color p (Color. 1.0 0.0 1.0 alpha) :dataset (+ 6 (* j 8)))
        ;; Add the hospital load
        (ic/add-lines p days (:hospitalizations totals))
        (ic/set-stroke-color p (Color. 0.3125 0.625 1.0 alpha) :dataset (+ 7 (* j 8)))
        (ic/add-lines p days [] #_ hospitalizations)
        (ic/set-stroke-color p (Color. 0.0 0.0 1.0 alpha) :dataset (+ 8 (* j 8)))))
    (i/view p)
    (.addLegend p (org.jfree.chart.title.LegendTitle. (.getPlot (plot-legend))))
    p))

(defn plot-avgs [sims & [p avg-only]]
  (let [j (if p (count sims) 0)
        p (or p (ic/xy-plot))
        sims (filter #(not (empty? (nth % 3))) sims)
        alpha 1.0
        max-days (inc (apply max (for [[_ data _ pc] sims
                                       :let [offset (second pc)]
                                       [k] data]
                                   (- k offset))))
        min-days (- (apply max (for [[_ _ _ pc] sims]
                                 (second pc))))
        rs (into {} (for [lbl [:contractions :illnesses :recoveries :deaths :hospitalizations]]
                      [lbl (apply map #(sort %&)
                                  (for [[_ data _ pc] sims
                                        :let [offset (second pc)]]
                                    (reductions + (map #(get-in data [% lbl] 0)
                                                         (range (+ offset min-days)
                                                                (+ offset max-days))))))]))
        totals (into {} (for [lbl [:contractions :illnesses :recoveries :deaths :hospitalizations]]
                          [lbl (vec (map avg (rs lbl)))]))
        low (into {} (for [lbl [:contractions :illnesses :recoveries :deaths :hospitalizations]]
                          [lbl (vec (map #(nth % (int (/ (count sims) 20))) (rs lbl)))]))
        high (into {} (for [lbl [:contractions :illnesses :recoveries :deaths :hospitalizations]]
                          [lbl (vec (map #(nth % (- (count sims) (int (/ (count sims) 20)) 1)) (rs lbl)))]))]
    ;; Add the cumulative lines
    (doseq [[lbl i c name] [[:contractions 1 (Color. (float 1.0) (float 0.7) (float 0.0) (float alpha)) "Exposed"]
                            [:illnesses 2 (Color. 1.0 0.0 0.0 alpha) "Sickened"]
                            [:recoveries 3 (Color. 0.0 1.0 0.0 alpha) "Recovered"]
                            [:deaths 4 (Color. 0.25 0.25 0.25 alpha) "Dead"]]]
      (plot-line p (range min-days max-days) (lbl totals) c 4 (+ i (* j 8)) name))
    ;; Add the healthy line
    (plot-line p [] [] (Color. 1.0 1.0 1.0 alpha) 4 (+ 5 (* j 8)) "Susceptible")
    ;; Add the transmissive cases
    (plot-line p [] [] (Color. 1.0 0.0 1.0 alpha) 4 (+ 6 (* j 8)) "Infectious")
    ;; Add the hospital load
    (plot-line p (range min-days max-days) (:hospitalizations totals) (Color. 0.3125 0.625 1.0 alpha) 4 (+ 7 (* j 8)) "Hospitalized")
    (plot-line p [] [] (Color. 0.0 0.0 1.0 alpha) 4 (+ 8 (* j 8)) "")
    (when (not avg-only)
      (doseq [[lbl i c] [[:contractions 9 (Color. (float 1.0) (float 0.7) (float 0.0) (float alpha))]
                         [:illnesses 10 (Color. 1.0 0.0 0.0 alpha)]
                         [:recoveries 11 (Color. 0.0 1.0 0.0 alpha)]
                         [:deaths 12 (Color. 0.0 0.0 0.0 alpha)]]]
        (plot-line p (range min-days max-days) (lbl low) (.brighter c) 1 (+ i (* j 8))) "")
      ;; Add the healthy line
      (plot-line p [] [] (.brighter (Color. 1.0 1.0 1.0 alpha)) 1 (+ 13 (* j 8)) "")
      ;; Add the transmissive cases
      (plot-line p [] [] (.brighter (Color. 1.0 0.0 1.0 alpha)) 1 (+ 14 (* j 8)) "")
      ;; Add the hospital load
      (plot-line p (range min-days max-days) (:hospitalizations low) (.brighter (Color. 0.3125 0.625 1.0 alpha)) 1 (+ 15 (* j 8)) "")
      (plot-line p [] [] (.brighter (Color. 0.0 0.0 1.0 alpha)) 1 (+ 16 (* j 8)) "")
      (doseq [[lbl i c] [[:contractions 17 (Color. (float 1.0) (float 0.7) (float 0.0) (float alpha))]
                         [:illnesses 18 (Color. 1.0 0.0 0.0 alpha)]
                         [:recoveries 19 (Color. 0.0 1.0 0.0 alpha)]
                         [:deaths 20 (Color. 0.0 0.0 0.0 alpha)]]]
        (plot-line p (range min-days max-days) (lbl high) (.darker c) 1 (+ i (* j 8))) "")
      ;; Add the healthy line
      (plot-line p [] [] (.darker (Color. 1.0 1.0 1.0 alpha)) 1 (+ 21 (* j 8)) "")
      ;; Add the transmissive cases
      (plot-line p [] [] (.darker (Color. 1.0 0.0 1.0 alpha)) 1 (+ 22 (* j 8)) "")
      ;; Add the hospital load
      (plot-line p (range min-days max-days) (:hospitalizations high) (.darker (Color. 0.3125 0.625 1.0 alpha)) 1 (+ 23 (* j 8)) "")
      (plot-line p [] [] (.darker (Color. 0.0 0.0 1.0 alpha)) 1 (+ 24 (* j 8))) "")
    #_(ic/add-lines p atl-range atl-hospitalizations)
    #_(ic/set-stroke-color p (Color. 0 127 127) :dataset (+ 1 (* (count sims&alignments) 8)))
    #_(ic/set-stroke p :width 13 :dataset (+ 1 (* (count sims&alignments) 8)))
    (i/view p)
    p))

(defn plot-deaths [sims & [alignments title x-axis actuals actuals-range]]
  (let [p (ic/xy-plot [] [] :title title :x-label x-axis :y-label "Population")
        sims&alignments (map vector (range) sims (or alignments (repeat (count sims) 0)))
        alpha (float (/ (Math/pow (count sims) 0.75)))
        avg-ds (avg-sims sims alignments)]
    (doseq [[j [actors data] offset] sims&alignments]
      (let [offset (or offset 0)
            max-days (inc (apply max (keys data)))
            days (range (- offset) (- max-days offset))
            sorted-data (sort data)
            death-totals (vec (reductions + (map #(get-in data [% :deaths] 0) (range max-days))))]
        ;; Add the cumulative lines
        (ic/add-lines p days death-totals)
        (ic/set-stroke-color p (Color. 0.0 0.0 0.0 alpha) :dataset (+ 1 j))))
    (ic/add-lines p (i/sel avg-ds :cols :aligned-day) (i/sel avg-ds :cols :deaths-sum))
    (ic/set-stroke-color p (Color. 0 0 0) :dataset (+ 1 (count sims)))
    (ic/set-stroke p :width 5 :dataset (+ 1 (count sims)))
    (ic/add-points p actuals-range actuals)
    (i/view p)
    (.addLegend p (org.jfree.chart.title.LegendTitle. (.getPlot (plot-legend-deaths))))
    p))

(defn plot-hospitalizations [sims & [alignments title x-axis actuals actuals-range p ds]]
  (let [p (or p (ic/xy-plot [] [] :title title :x-label x-axis :y-label "Population"))
        ds (or ds 0)
        sims (filter #(not (empty? (nth % 3))) sims)
        sims&alignments (map vector (drop 1 (range)) sims (or alignments (repeat (count sims) 0)))
        max-days (inc (apply max (for [[_ [_ data] offset] sims&alignments
                                       [k] data]
                                   (- k offset))))
        min-days (- (apply max (for [[_ _ offset] sims&alignments]
                                 offset)))
        avgs (vec (apply map #(avg %&)
                             (for [[_ [_ data] offset] sims&alignments]
                               (reductions + (map #(- (get-in data [% :hospitalizations] 0)
                                                      (get-in data [% :discharges] 0)
                                                      (get-in data [% :deaths] 0))
                                                  (range (+ offset min-days)
                                                         (+ offset max-days)))))))
        census-avgs (vec (apply map #(avg %&)
                                (for [[_ [_ data] offset] sims&alignments]
                                  (reductions + (map #(get-in data [% :hospitalizations] 0)
                                                     (range (+ offset min-days)
                                                            (+ offset max-days)))))))
        alpha (float (/ (Math/pow (count sims) 0.75)))]
    (doseq [[j [actors data] offset] sims&alignments]
      (let [offset (or offset 0)
            max-days (inc (apply max (keys data)))
            days (range (- offset) (- max-days offset))
            sorted-data (sort data)
            hospitalizations (reductions +
                                         (map #(- %1 %2)
                                                (map #(get-in data [% :hospitalizations] 0) (range max-days))
                                                (map #(+ (get-in data [% :discharges] 0)
                                                         (get-in data [% :deaths] 0)) (range max-days))))
            census (reductions +
                               (map #(get-in data [% :hospitalizations] 0) (range max-days)))]
        ;; Add the hospital load
        (plot-line p days hospitalizations (Color. 0.0 0.0 1.0 alpha) 1 (+ ds -1 (* 2 j)))
        (plot-line p days census (Color. 0.0 0.8 0.8 alpha) 1 (+ ds (* 2 j)))))
    (plot-line p (range min-days max-days) avgs (Color. 0.0 0.0 1.0) 4 (+ ds 1 (* 2 (count sims))))
    (plot-line p (range min-days max-days) census-avgs (Color. 0.0 0.50 0.50) 4 (+ ds 2 (* 2 (count sims))))
    (ic/add-points p actuals-range actuals)
    ;(ic/set-stroke-color p (Color. 0 127 127) :dataset (+ 1 (* (count sims&alignments))))
    ;(ic/set-stroke p :width 13 :dataset (+ 1 (* (count sims&alignments))))
    (.addLegend p (org.jfree.chart.title.LegendTitle. (.getPlot (plot-legend-hospitalizations))))
    (i/view p)
    p))

(defn save-plot [p filename]
  (i/save p (str filename ".png") :width 1000 :height 800)
  (isvg/save-svg p (str filename ".svg") :width 1000 :height 800)
  (ipdf/save-pdf p (str filename ".pdf") :width 1000 :height 800))

(defn save-data [sims filename & [offsets]]
  (let [offsets (or offsets (repeat nil))
        sums (map summarize sims offsets)
        sum-ds (i/dataset #_[:id :policy-change-1 :policy-change-2 :eradication-days :aligned-eradication-days
                           :total-infected :total-hospitalizations :total-deaths :peak-hospitalizations-count
                           :peak-hospitalizations-day :aligned-peak-hospitalizations-day
                           :peak-illnesses-count :peak-illnesses-day :aligned-peak-illness-day
                           :peak-recoveries-count :peak-recoveries-day :aligned-peak-recoveries-day]
                          (for [id (range (count sums))
                                :let [sum (nth sums id)]]
                            (assoc sum :id id)))
        max-days (reduce #(max %1 (:aligned-eradication-days %2)) 0 sums)
        min-days (- (reduce #(max %1 (:alignment-offset %2)) 0 sums))
        days (range min-days max-days)
        daily-ds (i/dataset #_[:id :day :exposures :illnesses :hospitalizations :discharges
                             :recoveries :deaths]
                            (for [id (range (count sims))
                                  :let [offset (last (nth (nth sims id) 3))
                                        offset-days (map #(+ % offset) days)
                                        dailies (map (second (nth sims id)) offset-days)
                                        totals (reductions #(merge-with + %1 %2) dailies)]
                                  [day day-data total-data] (map vector days dailies totals)]
                              {:run-id id, :aligned-day day,
                               :exposures (get day-data :contractions 0)
                               :illnesses (get day-data :illnesses 0)
                               :hospitalizations (get day-data :hospitalizations 0)
                               :discharges (get day-data :discharges 0)
                               :recoveries (get day-data :recoveries 0)
                               :deaths (get day-data :deaths 0)
                               :exposures-sum (get total-data :contractions 0)
                               :illnesses-sum (get total-data :illnesses 0)
                               :hospitalizations-sum (get total-data :hospitalizations 0)
                               :discharges-sum (get total-data :discharges 0)
                               :recoveries-sum (get total-data :recoveries 0)
                               :deaths-sum (get total-data :deaths 0)}))
        avg-ds (apply i/conj-cols
                      (for [col (disj (into #{} (i/col-names daily-ds)) :run-id :aligned-day)]
                        (->> daily-ds
                             (i/$rollup :mean col :aligned-day)
                             (i/$order :aligned-day :asc))))
        avg-ds (i/dataset (i/col-names avg-ds) (i/$map #(map float %&) (i/col-names avg-ds) avg-ds))]
    (i/save sum-ds (str filename "summaries.csv"))
    (i/save daily-ds (str filename "daily.csv"))
    (i/save avg-ds (str filename "avg.csv"))))

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

(defn summarize [[actors data totals policy-change-days] & [offset]]
  (let [eradication-days (apply max (keys data))
        terminal-day (apply max (keys totals))
        total-infected (get-in totals [terminal-day :contractions] 0) #_(reduce + (map #(get % :contractions 0) (vals data)))
        sorted-data (sort data)
        peak-illnesses (reduce #(if (>= (second %1) (second %2)) %1 %2)
                               (->> terminal-day
                                    inc
                                    range
                                    (map totals)
                                    (map #(- (get % :illnesses 0) (get % :recoveries 0) (get % :deaths 0)))
                                    (map-indexed vector))
                               #_(map vector (map first sorted-data) (reductions 
                                                        #(+ %1 (- (get %2 :illnesses 0) (get %2 :recoveries 0)))
                                                        0 (map second sorted-data))))
        peak-recoveries (reduce #(if (>= (second %1) (second %2)) %1 %2)
                               (->> terminal-day
                                    inc
                                    range
                                    (map data)
                                    (map #(get % :recoveries 0))
                                    (map-indexed vector))
                               #_(map vector (keys data) (map #(- (get % :recoveries 0) (get % :illnesses 0)) (vals data))))
        total-deaths (-> terminal-day totals :deaths) #_(reduce + (map #(get % :deaths 0) (vals data)))
        peak-hospitalizations (reduce #(if (>= (second %1) (second %2)) %1 %2)
                               (->> terminal-day
                                    inc
                                    range
                                    (map totals)
                                    (map #(- (get % :hospitalizations 0) (get % :discharges 0) (get % :deaths 0)))
                                    (map-indexed vector))
                               #_(map vector (map first sorted-data)
                                           (reductions
                                            #(+ %1 (- (get %2 :hospitalizations 0) (+ (get %2 :discharges 0)
                                                                                      (get %2 :deaths 0))))
                                            0 (map second sorted-data))))
        total-hospitalizations (get-in totals [terminal-day :hospitalizations] 0) #_(reduce + (map #(get % :contractions 0) (vals data)))
        offset (or offset (last policy-change-days))]
    {:eradication-days eradication-days,
     :aligned-eradication-days (- eradication-days offset)
     :total-infected total-infected,
     :total-hospitalizations total-hospitalizations,
     :peak-illnesses-day (first peak-illnesses),
     :aligned-peak-illnesses-day (- (first peak-illnesses) offset)
     :peak-illnesses-count (second peak-illnesses),
     :peak-recoveries-day (first peak-recoveries),
     :aligned-peak-recoveries-day (- (first peak-recoveries) offset),
     :peak-recoveries-count (second peak-recoveries),
     :policy-change-1 (first policy-change-days)
     :policy-change-2 (second policy-change-days)
     :policy-change-3 (last policy-change-days)
     :total-deaths total-deaths,
     :peak-hospitalizations-day (first peak-hospitalizations)
     :aligned-peak-hospitalizations-day (- (first peak-hospitalizations) offset)
     :peak-hospitalizations-count (second peak-hospitalizations)
     :alignment-offset offset}))

;; hospitalization data for all of georgia, and approximated for Atlanta by prorating by deaths
;;                    March 25  26  27  28  29  30  31                            
;;                                               April   1    2    3    4    5    6    7    8    9   10
;;                     Day  -9  -8  -7  -6  -5  -4  -3  -2   -1    0    1    2    3    4    5    6    7
(def ga-hospitalizations  [394 473 566 617 666 707 833 952 1056 1158 1239 1283 1332 1774 1993 2159 2351 2479 2505 2589 2769 2922 3108 3324 3420 3464 3550 3779 3959 4069])
(def atl-hospitalizations [171 172 296 316 333 360 420 488  543  611  664  691  643  810  899  966 1055 1102 1116 1154 1252 1339 1405 1515 1566 1589 1613 1714 1785 1806])
(def atl-deaths           [ 20  20  34  40  41  52  63  79   90  104  111  118  141  158  166  183  189  192  197  197  237  264  279  304  309  316  349  371  381  391])
(def atl-actuals-range (range -9 (+ (count atl-deaths) -9)))

;; hospitalization and death data for San Diego County, CA.
;;                               *           *
;;                  March 17 18 19 20 21 22 23 24 25 26 27  28  29  30  31
;;                                                                   April   1   2   3   4   5   6   7
(def sd-hospitalizations [11 13 27 34 41 37 45 59 69 85 96 106 118 136 157 181 211 229 249 269 289 316])
(def sd-deaths           [ 0  0  0  0  1  1  2  2  3  5  7   7   7   9  10  16  17  18  19  19  31  36])

;; death data for Chicago, IL.
;;      March     22  23 24 25  26  27  28  29  30  31
;;                                               April  1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20  21  22
(def chi-deaths [nil nil 4  5 nil nil  15  15 nil  26 nil  43 nil nil nil  98 118 177 196 196 212 258 277 308 347 386 420 488 500 538 593 627])

(defn avg
  ([x] (/ (reduce + 0.0 x) (float (count x))))
  ([x y] (let [x&y (filter (fn [[x y]] (and x y)) (map vector x y))]
                     (/ (reduce + 0.0 (map (partial apply *) x&y)) (reduce #(+ %1 (second %2)) 0.0 x&y)))))

(defn score [[_ _ totals pc]]
            (let [offset (+ (or (first pc) 0) 2)
                  hs (map #(get % :hospitalizations 0) (take (count atl-hospitalizations) (drop offset (map totals (range)))))]
                 (Math/sqrt (/ (reduce + (map #(* % %) (map - atl-hospitalizations hs))) (count atl-hospitalizations)))))

(defn avg-sims [sims & [alignment]]
  (let [alignment (or alignment (repeat nil))
        sums (map summarize sims alignment)
        max-days (reduce #(max %1 (:aligned-eradication-days %2)) 0 sums)
        min-days (- (reduce #(max %1 (:alignment-offset %2)) 0 sums))
        days (range min-days max-days)
        daily-ds (i/dataset #_[:id :day :exposures :illnesses :hospitalizations :discharges
                             :recoveries :deaths]
                            (for [id (range (count sims))
                                  :let [offset (or (nth alignment id) (last (nth (nth sims id) 3)))
                                        offset-days (map #(+ % offset) days)
                                        dailies (map (second (nth sims id)) offset-days)
                                        totals (reductions #(merge-with + %1 %2) dailies)]
                                  [day day-data total-data] (map vector days dailies totals)]
                              {:run-id id, :aligned-day day,
                               :exposures (get day-data :contractions 0)
                               :illnesses (get day-data :illnesses 0)
                               :hospitalizations (get day-data :hospitalizations 0)
                               :discharges (get day-data :discharges 0)
                               :recoveries (get day-data :recoveries 0)
                               :deaths (get day-data :deaths 0)
                               :exposures-sum (get total-data :contractions 0)
                               :illnesses-sum (get total-data :illnesses 0)
                               :hospitalizations-sum (get total-data :hospitalizations 0)
                               :discharges-sum (get total-data :discharges 0)
                               :recoveries-sum (get total-data :recoveries 0)
                               :deaths-sum (get total-data :deaths 0)}))
        avg-ds (apply i/conj-cols
                      (for [col (disj (into #{} (i/col-names daily-ds)) :run-id :aligned-day)]
                        (->> daily-ds
                             (i/$rollup :mean col :aligned-day)
                             (i/$order :aligned-day :asc))))
        avg-ds (i/dataset (i/col-names avg-ds) (i/$map #(map float %&) (i/col-names avg-ds) avg-ds))]
    avg-ds))

(defn sims->dataset [sims alignment]
  (let [min-days (- (apply max alignment))
        max-days (apply max (map #(- (apply max (keys (nth %1 2))) %2) sims alignment))]
    (i/dataset (for [day (range min-days max-days)
                     [id sim offset] (map vector (range) sims alignment)
                     :let [totals (get-in sim [2 (+ day offset)] {})]]
                 (into {:id id, :day day}
                       (for [lbl [:illnesses :hospitalizations :discharges :deaths :recoveries]]
                         [lbl (get totals lbl 0)]))))))

(defn stats [sims alignment day lbl]
  (let [ds (sims->dataset sims alignment)
        n (dec (count sims))
        data (sort (i/sel (i/$where {:day day} ds) :cols lbl))
        p05 (* 0.05 n)
        p50 (* 0.5 n)
        p95 (* 0.95 n)]
    (vec (map #(avg [(nth data (int %)) (nth data (inc (int %)))] [(- % (int %)) (- (inc (int %)) %)])
              [p05 p50 p95]))))
