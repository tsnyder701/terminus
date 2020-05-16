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

(defn sel-metro [dataset metro]
  (->> dataset
       (i/$join [["County Name" "State"] ["County Name" "State"]] us-metros)
       (i/$where {"Metro Area" metro})))

(defn metro-pop [metro]
  (reduce + (i/sel (sel-metro us-pop metro) :cols "population")))

(defn metro-deaths [metro]
  (into (sorted-map) (kvmap #(.getDayOfYear (LocalDate/parse % (DateTimeFormatter/ofPattern "M/d/yy"))) (partial apply +) (ds/to-map (i/sel (sel-metro us-deaths metro) :except-cols ["\ufeffcountyFIPS" "countyFIPS" "County Name" "State" "stateFIPS" "Metro Area"])))))
