(ns covid.core
  (:require [clojure.set :as set])
  (:import [java.time LocalDate Month]))

(defn map-date
  ([first-date data]
   (let [first-date (or first-date (LocalDate/of 2020 Month/MARCH 1))
         dates (iterate #(.plusDays % 1) first-date)]
     (into {} (map vector dates data))))
  ([data] (map-date nil data)))

(def +pop+ {:us 350000000, :ga 6000000, :cobb 750000})
(def +daily-tests+ {:us (map-date [239 534 760 1083 1569 1840 1416 1536 3023 3131
                                   3906 5468 6214 5494 5270 9353 9433])})
(def +cum-cases+ {:us (map-date [30 53 80 98 164 214 279 423 647 937
                                   1215 1629 1896 2234 3487 4226 7038 10442 15219 18747
                                   24583 33404 44183]),
                  :ga (map-date (LocalDate/of 2020 Month/MARCH 8)
                                [11 15 17 27 33 64 66 99 121 146 197 287 420 555 620 800 1097]),
                  :cobb (map-date (LocalDate/of 2020 Month/MARCH 7)
                                  [1 2 3 4 6 9 15 16 19 22 25 28 37 47 50 67 79 90])})
(def +cum-onset+ {:us (map-date [125 147 179 183 204 249 280 379 559 523 628 741 802])})
(def +cum-deaths+ {:us (map-date (LocalDate/of 2020 Month/MARCH 11)
                                 [28 30 40 47 57 69 85 108 150 150 260 340 471 590]),
                   :ga (map-date (LocalDate/of 2020 Month/MARCH 17)
                                 [1 1 10 13 20 25 26 38])})

(def isolation-severity 0.5)
(def actor-keys [:id :cluster-types :clusters])
(def cluster-keys [:id :type :size :freq :trasmission-rate :persistence :members])
(defn make-graph [actors clusters]
  (let [actor-ids-by-cluster-type (apply merge-with set/union
                                      (for [a actors]
                                        (into {} (map vector (:cluster-types a) (repeat #{(:id a)})))))
        shuffled-ids (into {} (map #(vector (key %1) (shuffle (val %1))) actor-ids-by-cluster-type))]
    (println "step 1")
    (loop [i 0
           actors (vec actors)
           clusters (vec clusters)
           abct shuffled-ids]
      (if (zero? (mod i 100)) (println i))
      (if (>= i (count clusters))
        [actors clusters]
        (let [c (nth clusters i)
              members (take (:size c) (shuffle ((:type c) abct)))]
          (recur (inc i)
                 (reduce #(update-in %1 [%2 :clusters] (comp vec conj) (:id c)) actors members)
                 (assoc-in clusters [i :members] members)
                 (update abct (:type c) (partial drop (count members)))))))))

(defn make-actors [n cluster-type-membership]
  (vec (for [i (range n)]
         {:id i, :cluster-types (reduce #(if (> (second %2) (rand)) (conj %1 (first %2)) %1) [] cluster-type-membership)})))

(defn make-clusters [actors cluster-type-size-distrib]
  (let [ct-member-counts (apply merge-with + (for [a actors
                                                   ct (:cluster-types a)]
                                               {ct 1}))]
    (loop [id 0
           ct-member-counts ct-member-counts
           clusters []]
      (if (empty? ct-member-counts)
        clusters
        (let [[ct mc] (first ct-member-counts)
              cmc (reduce #(if (< %1 (first %2)) (reduced (second %2)) %1) (rand) (cluster-type-size-distrib ct))]
          (if (< mc (second (first (cluster-type-size-distrib ct))))
            (recur id (dissoc ct-member-counts ct) clusters)
            (if (> cmc mc)
              (recur id ct-member-counts clusters)
              (recur (inc id) (update ct-member-counts ct - cmc) (conj clusters {:id id :type ct :size cmc})))))))))

(defn run-simulation [[actors clusters] cluster-type-transmission-by-day]
  (loop [actors (update actors (rand-int (count actors))
                        assoc :contract-day 0, :severity 0.5, :illness-day 5, :recovery-day 20, :source -1)
         day 1
         max-day 20
         cttd cluster-type-transmission-by-day]
    (let [infections (apply merge (for [a actors
                                        ;; You can only transmit if you've contracted the virus
                                        ;; but haven't recovered or died from it yet.
                                        :when (<= (get a :contract-day 1e6)
                                                  day
                                                  (or (get a :recovery-day) (get a :death-day) 1e6))
                                        cluster (map clusters (:clusters a))
                                        ;; In order to transmit you mustn't be symptomatic yet, or
                                        ;; the severity is low enough that you still go out, or
                                        ;; we're considering the family cluster, who can still
                                        ;; get it even when you don't go out.
                                        :when (or (< day (get a :illness-day 1e6))
                                                  (= :family (:type cluster))
                                                  (< isolation-severity (:severity a)))
                                        member-id (:members cluster)
                                        ;; Finally, the other actor you're transmitting to must not have
                                        ;; already contracted it, and they must be randomly unlucky enough
                                        ;; to be exposed based upon the transmission rate for the location.
                                        :when (and (< (rand) ((first cttd) (:type cluster)))
                                                   (< day (get-in actors [member-id :contract-day] 1e6)))]
                                    (let [severity (rand)  ;; uniform random
                                          incubation (rand-int 10)  ;; [0, 9] days of incubation
                                          ;; [7, 34] days of illness for most severe cases
                                          ;; [2, 12] days for the least severe still having symptoms
                                          illness (int (* severity (+ 7 (rand-int 28)))) 
                                          terms (conj {}
                                                      [:contract-day day]
                                                      [:severity severity]
                                                      [:source (:id a)]
                                                      ;; 30% of cases considered asymptomatic
                                                      (if (< 0.3 severity)
                                                        [:illness-day (+ day incubation)])
                                                      ;; 2% of cases result in death
                                                      (if (< 0.98 severity)
                                                        [:death-day (+ day incubation illness)]
                                                        [:recovery-day (+ day incubation illness)]))]
                                      #_(println "day" day ":" (:id a) "->" member-id "at" (dissoc cluster :members))
                                      {member-id terms})))
          actors (reduce #(update %1 (first %2) (partial apply conj) (second %2)) actors infections)
          new-days (flatten (map (comp vals #(select-keys % [:death-day :recovery-day])) (vals infections)))
          max-day (reduce max max-day new-days)]
      (println day ":" (count infections) "new cases")
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
        (recur actors (inc day) max-day (next cttd))))))

(defn plot-sim [[actors data]]
  (let [p (incanter.charts/xy-plot)
        max-days (inc (apply max (keys data)))]
    ;; Add the cumulative lines
    (doseq [lbl [:contractions :illnesses :recoveries :deaths]]
              (add-lines p
               (range max-days)
               (map #(apply + (map (fn [a] (get-in data [a lbl] 0)) (range %1))) (range max-days))))
    ;; Add the healthy line
    (add-lines p (range max-days) (map #(apply - (count actors) 0 (map (fn [a] (get-in (second sim) [a :contractions] 0)) (range %1))) (range max-days)))
    ;; Add the transmissive cases
    (add-lines p (range max-days) (map (fn [day] (count (filter #(< (get %1 :contract-day 1e6) day (inc (or (get %1 :death-day) (get %1 :recovery-day) 1e6))) (first sim)))) (range max-days)))
    ;; Add the hospital load
    (add-lines p (range max-days) (map (fn [day] (* 0.2 (count (filter #(<= (get %1 :illness-day 1e6) day (or (get %1 :death-day) (get %1 :recovery-day))) (first sim))))) (range max-days)))
    (view p)))
