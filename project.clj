(defproject me.arrdem/clucy "0.4.2-SNAPSHOT"
  :description "A Clojure interface to the Lucene search engine"
  :url "http://github/weavejester/clucy"
  :dependencies [[org.clojure/clojure "1.7.0"]
                 [org.apache.lucene/lucene-core "4.10.4"]
                 [org.apache.lucene/lucene-queryparser "4.10.4"]
                 [org.apache.lucene/lucene-analyzers-common "4.10.4"]
                 [org.apache.lucene/lucene-highlighter "4.10.4"]]
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :profiles {:1.4  {:dependencies [[org.clojure/clojure "1.4.0"]]}
             :1.5  {:dependencies [[org.clojure/clojure "1.5.0"]]}
             :1.6  {:dependencies [[org.clojure/clojure "1.6.0"]]}
             :1.7  {:dependencies [[org.clojure/clojure "1.7.0"]]}}
  :codox {:src-dir-uri "http://github/weavejester/clucy/blob/master"
          :src-linenum-anchor-prefix "L"})
