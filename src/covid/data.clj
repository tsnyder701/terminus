(ns covid.data
  (:require [incanter.core :as i]
            [incanter.io :as io]
            [clojure.core.matrix.dataset :as ds])
  (:use [covid.util])
  (:import [java.time.format DateTimeFormatter]
           [java.time LocalDate]))

(def us-cases (io/read-dataset "data/covid_confirmed_usafacts.csv" :header true :keyword-headers false))
(def us-deaths (io/read-dataset "data/covid_deaths_usafacts.csv" :header true :keyword-headers false))
(def us-pop (io/read-dataset "data/covid_county_population_usafacts.csv" :header true :keyword-headers false))
(def us-metros (io/read-dataset "data/metros.csv" :header true :keyword-headers false))
(def us-states (into (sorted-set) (i/sel us-deaths :cols "State")))

(defn sel-metro [dataset metro]
  (->> dataset
       (i/$join [["County Name" "State"] ["County Name" "State"]] us-metros)
       (i/$where {"Metro Area" metro})))

(defn metro-pop [metro]
  (reduce + (i/sel (sel-metro us-pop metro) :cols "population")))

(defn metro-deaths [metro]
  (into (sorted-map) (kvmap #(.getDayOfYear (LocalDate/parse % (DateTimeFormatter/ofPattern "M/d/yy"))) (partial apply +) (ds/to-map (i/sel (sel-metro us-deaths metro) :except-cols ["\ufeffcountyFIPS" "countyFIPS" "County Name" "State" "stateFIPS" "Metro Area"])))))

(defn sel-state [dataset state]
  (i/$where {"State" state} dataset))

(defn state-pop [state]
  (let [pops (i/sel (sel-state us-pop state) :cols "population")]
    (if (sequential? pops)
      (reduce + pops)
      pops)))

(defn state-deaths [state]
  (into (sorted-map) (kvmap #(.getDayOfYear (LocalDate/parse % (DateTimeFormatter/ofPattern "M/d/yy"))) (partial apply +) (ds/to-map (i/sel (sel-state us-deaths state) :except-cols ["\ufeffcountyFIPS" "countyFIPS" "County Name" "State" "stateFIPS"])))))

(defn state-cases [state]
  (into (sorted-map) (kvmap #(.getDayOfYear (LocalDate/parse % (DateTimeFormatter/ofPattern "M/d/yy"))) (partial apply +) (ds/to-map (i/sel (sel-state us-cases state) :except-cols ["\ufeffcountyFIPS" "countyFIPS" "County Name" "State" "stateFIPS"])))))

(defn state-fips [state]
  (let [fips (i/sel (sel-state us-deaths state) :cols "stateFIPS")]
    (if (nil? fips)
      "??"
      (if (sequential? fips)
        (format "%02d" (first fips))
        (format "%02d" fips)))))

(defn day-of-year [date-str]
  (.getDayOfYear (LocalDate/parse date-str (DateTimeFormatter/ofPattern "M/d/yy"))))

(defn date [day-of-year]
  (.format (LocalDate/ofYearDay 2020 day-of-year) (DateTimeFormatter/ofPattern "M/d/yy")))

(defn date-iso [day-of-year]
  (.format (LocalDate/ofYearDay 2020 day-of-year) (DateTimeFormatter/ofPattern "yyyy-MM-dd")))

(def ga-model {:state "GA", :ld-day 94, :ranges [[0.01 0.024 0.0001]
                                                 [0.003 0.011 0.00001]
                                                 [0.002 0.01 0.00001]]
               :policy-fn (fn [a0 a1 a2]
                            [[#(<= 20 (get-in %3 [%1 :deaths] 0)) a0]
                             [#(<= 185 (get-in %3 [%1 :deaths] 0)) a1]
                             [#(<= 21 (get-in %3 [%1 :policy-2-day] 0)) a2]
                             [(constantly false) (* 1 a2)]])
               :offset-fn #(- (or (second (nth % 3)) 100) 94)})

(def fl-model {:state "FL", :ld-day 94, :ranges [[0.01 0.024 0.0001]
                                                 [0.003 0.011 0.00001]
                                                 [0.002 0.01 0.00001]]
               :policy-fn (fn [a0 a1 a2]
                            [[#(<= 20 (get-in %3 [%1 :deaths] 0)) a0]
                             [#(<= 158 (get-in %3 [%1 :deaths] 0)) a1]
                             [#(<= 21 (get-in %3 [%1 :policy-2-day] 0)) a2]
                             [(constantly false) (* 1 a2)]])
               :offset-fn #(- (or (second (nth % 3)) 100) 94)})

(def ca-model {:state "CA", :ld-day 79, :ranges [[0.016 0.02 0.0001]
                                                 [0.007 0.008 0.00001]
                                                 [25 29 1]
                                                 [-0.2 -0.1 0.001]]
               :policy-fn (fn [a0 a1 m0 s2]
                            [[#(<= 22 (get-in %3 [%1 :deaths] 0)) a0]
                             [#(<= m0 (get-in %3 [%1 :policy-1-day])) a1]
                             [(constantly false) (* a1 (Math/exp s2))]])
               :offset-fn #(- (or (first (nth % 3)) 100) 79)})

(def ny-model {:state "NY", :ld-day 76, :ranges [[0.02 0.04 0.00001]
                                                 [0.004 0.009 0.00001]]
               :policy-fn (fn [a0 a1]
                            [[#(<= 116 (get-in %3 [%1 :deaths] 0)) a0]
                             [(constantly false) (* 1 a1)]])
               :offset-fn #(- (or (first (nth % 3)) 100) 82)})

(def nj-model {:state "NJ", :ld-day 78, :ranges [[75 100 1]
                                                 [0.01 0.06 0.0001]
                                                 [0 20 1]
                                                 [0.001 0.018 0.00001]
                                                 [-0.8 0.2 0.01]]})

(def wa-model {:state "WA", :ld-day 76})
(def mi-model {:state "MI", :ld-day 83})
(def tx-model {:state "TX", :ld-day 81})
(def co-model {:state "CO", :ld-day 83})

(def us-models
  (let [specific-models [ga-model fl-model ca-model ny-model nj-model wa-model mi-model tx-model co-model]
        generic-mo (vec (map #(hash-map :state %) (reduce #(disj %1 (:state %2)) us-states specific-models)))]
    (apply conj generic-mo specific-models)))
