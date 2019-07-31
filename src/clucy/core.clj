(ns clucy.core
  (:import (java.io StringReader File)
           (org.apache.lucene.analysis Analyzer TokenStream)
           (org.apache.lucene.analysis.standard StandardAnalyzer)
           (org.apache.lucene.document Document Field Field$Index Field$Store)
           (org.apache.lucene.index IndexWriter IndexReader Term
                                    IndexWriterConfig
                                    IndexWriterConfig$OpenMode
                                    DirectoryReader FieldInfo)
           (org.apache.lucene.queryparser.classic QueryParser)
           (org.apache.lucene.search BooleanClause BooleanClause$Occur
                                     BooleanQuery IndexSearcher Query ScoreDoc
                                     Scorer TermQuery MatchAllDocsQuery)
           (org.apache.lucene.search.highlight Highlighter QueryScorer
                                               SimpleHTMLFormatter)
           (org.apache.lucene.util Version AttributeSource)
           (org.apache.lucene.store NIOFSDirectory RAMDirectory Directory)))

(def ^{:dynamic true} *version*
  Version/LUCENE_CURRENT)

(def ^{:dynamic true} *analyzer*
  (StandardAnalyzer. *version*))

;; To avoid a dependency on either contrib or 1.2+
(defn as-str ^String [x]
  (if (keyword? x)
    (name x)
    (str x)))

(defn as-dir ^File [x]
  (if-not (instance? File x)
    (if (string? x)
      (File. x)
      (throw (Exception. "Expects a java.{io.File,lang.String}")))
    x))

;; flag to indicate a default "_content" field should be maintained
(def ^{:dynamic true} *content*
  true)

(defn memory-index
  "Create a new index in RAM."
  []
  (RAMDirectory.))

(defn disk-index
  "Create a new index in a directory on disk. Dir should be a File or
  a String, either must name a directory which exists."
  [dir]
  (let [^File d (as-dir dir)]
    (NIOFSDirectory. d)))

(defn index-writer
  "Create an IndexWriter."
  ^IndexWriter [index]
  (let [iwcfg (IndexWriterConfig. *version* *analyzer*)]
    (.setOpenMode iwcfg IndexWriterConfig$OpenMode/CREATE_OR_APPEND)
    (IndexWriter. index iwcfg)))

(defn index-reader
  "Create an IndexReader."
  ^IndexReader [index]
  (DirectoryReader/open ^Directory index))


;; We want to hold IndexWriters open for performance, but we can't
;; actually have multiple IndexWriters open on a single index.
;;
;; Thankfully IndexWriters are thread safe.
;;
;; As a result we can safely "open" both a Reader and a Writer for any
;; given Index, and maintain a cache mapping from Index instance to a
;; (Reader, Writer, Index) structure which may be thread shared.

(defonce index-cache
  (atom {}))

;; We also want some common abstraction for working with either
;; a "real" open index or something we know how to open into either a
;; reader or writer

(defprotocol IIndex
  (as-reader [_])
  (as-writer [_])
  (as-index  [_]))

;; Now the tuple thing

(declare close-index)

(deftype AnIndex [reader writer ind]
  java.io.Closeable
  (close [this]
    (close-index this))

  IIndex
  (as-reader [_] reader)
  (as-writer [_] writer)
  (as-index  [_] ind))

;; Open tuple instances using the cache

(defn open-index [ind]
  (let [key (if (instance? NIOFSDirectory ind)
              (.getDirectory ind)
              ind)]
    (if-let [ai (get @index-cache key)]
      ai
      (let [iw (index-writer ind)]
        (. iw (flush true true))
        (try
          (let [ir (index-reader ind)
                ai (AnIndex. ir iw ind)]
            (swap! index-cache assoc key ai)
            ai)
          (catch Exception e
            (.close iw)
            (throw e)))))))

;; Close them invalidating the cache

(defn close-index [ind]
  {:pre [(instance? AnIndex ind)]}
  (let [key (if (instance? NIOFSDirectory ind)
              (.getDirectory ind)
              ind)]
    (.close (.reader ind))
    (.close (.writer ind))
    (swap! index-cache dissoc key)
    nil))

;; And extend this abstraction to the other interesting types

(extend-protocol IIndex
  NIOFSDirectory
  (as-reader [d]
    (as-reader (open-index d)))
  (as-writer [d]
    (as-writer (open-index d)))
  (as-index [d] d)

  IndexWriter
  (as-writer [d] d)

  IndexReader
  (as-reader [d] d)

  RAMDirectory
  (as-reader [d]
    (as-reader (open-index d)))
  (as-writer [d]
    (as-writer (open-index d)))
  (as-index [d] d))



(defn- add-field
  "Add a Field to a Document.
  Following options are allowed for meta-map:
  :stored - when false, then do not store the field value in the index.
  :indexed - when false, then do not index the field.
  :analyzed - when :indexed is enabled use this option to disable/eneble Analyzer for current field.
  :norms - when :indexed is enabled user this option to disable/enable the storing of norms."
  ([document key value]
   (add-field document key value {}))

  ([document key value meta-map]
   (let [stored?     (if (false? (:stored meta-map))
                       Field$Store/NO
                       Field$Store/YES)

         how-indexed (if (false? (:indexed meta-map))
                       Field$Index/NO
                       (case [(false? (:analyzed meta-map))
                              (false? (:norms meta-map))]
                         [false false]
                         ,,Field$Index/ANALYZED

                         [true false]
                         ,,Field$Index/NOT_ANALYZED

                         [false true]
                         ,,Field$Index/ANALYZED_NO_NORMS

                         [true true]
                         ,,Field$Index/NOT_ANALYZED_NO_NORMS))]
     (.add ^Document document
           (Field. ^String (as-str key)
                   ^String (as-str value)
                   ^Field$Store stored?
                   ^Field$Index how-indexed)))))

(defn- map-stored
  "Returns a hash-map containing all of the values in the map that
  will be stored in the search index."
  [map-in]
  (->> map-in
       (map (fn [item]
              (if (or (= nil (meta map-in))
                      (not= false
                            (:stored ((first item) (meta map-in)))))
                item)))
       (filter (complement nil?))
       (merge {})))

(defn- concat-values
  "Concatenate all the maps values being stored into a single string."
  [map-in]
  (apply str (interpose " " (vals (map-stored map-in)))))

(defn- map->document
  "Create a Document from a map."
  [map]
  (let [document (Document.)]
    (doseq [[key value] map]
      (add-field document key value (key (meta map))))
    (when *content*
      (add-field document :_content (concat-values map)))
    document))

(defn add
  "Add hash-maps to the search index."
  [index & maps]
  (let [writer (as-writer index)]
    (doseq [m maps]
      (.addDocument writer
                    (map->document m)))))

(defn delete
  "Deletes hash-maps from the search index."
  [index & maps]
  (let [writer (as-writer index)]
    (doseq [m maps]
      (let [^BooleanQuery query (BooleanQuery.)
            ^"[Lorg.apache.lucene.search.Query;" arr (into-array BooleanQuery [query])]
        (doseq [[key value] m]
          (.add query
                (BooleanClause.
                 (TermQuery.
                  (Term. (.toLowerCase (as-str key))
                         (.toLowerCase (as-str value))))
                 BooleanClause$Occur/MUST)))
        (. ^IndexWriter writer (deleteDocuments arr))))))

(defn- document->map
  "Turn a Document object into a map."
  ([^Document document score]
   (document->map document score (constantly nil)))

  ([^Document document score highlighter]
   (let [m         (->> (for [^Field f (.getFields document)]
                          [(keyword (.name f)) (.stringValue f)])
                        (into {}))

         ;; so that we can highlight :_content
         fragments (highlighter m)

         doc-map   (dissoc m :_content)

         doc-meta  (as-> document d
                     (for [^Field f           (.getFields d)
                           :let   [field-type (.fieldType f)]]
                       [(keyword (.name f))
                        {:indexed   (.indexed field-type)
                         :stored    (.stored field-type)
                         :tokenized (.tokenized field-type)}])
                     (into {} d)
                     (assoc d
                            :_fragments fragments
                            :_score score)
                     (dissoc d :_content))]
     (with-meta doc-map doc-meta))))

(defn- make-highlighter
  "Create a highlighter function which will take a map and return highlighted
  fragments."
  [^Query query ^IndexSearcher searcher config]
  (if config
    (let [indexReader (.getIndexReader searcher)
          scorer (QueryScorer. (.rewrite query indexReader))
          config (merge {:field :_content
                         :max-fragments 5
                         :separator "..."
                         :pre "<b>"
                         :post "</b>"}
                        config)
          {:keys [field max-fragments separator fragments-key pre post]} config
          highlighter (Highlighter. (SimpleHTMLFormatter. pre post) scorer)]
      (fn [m]
        (let [str (field m)
              token-stream (.tokenStream ^Analyzer *analyzer*
                                         (name field)
                                         (StringReader. str))]
          (.getBestFragments ^Highlighter highlighter
                             ^TokenStream token-stream
                             ^String str
                             (int max-fragments)
                             ^String separator))))
    (constantly nil)))

(defn search
  "Search the supplied index with a query string."
  [index query max-results
   & {:keys [highlight default-field default-operator page results-per-page]
      :or {page 0}}]
  (if (every? false? [default-field *content*])
    (throw (Exception. "No default search field specified"))
    (let [reader           (as-reader index)
          default-field    (or default-field :_content)

          searcher         (IndexSearcher. reader)

          parser           (doto (QueryParser. *version*
                                               (as-str default-field)
                                               *analyzer*)
                             (.setDefaultOperator
                              (case (or default-operator :or)
                                :and
                                ,,QueryParser/AND_OPERATOR

                                :or
                                ,,QueryParser/OR_OPERATOR)))

          max-results      (if (= query :all)
                             Integer/MAX_VALUE
                             max-results)

          results-per-page (or results-per-page max-results)

          query            (if (= query :all)
                             (MatchAllDocsQuery.)
                             (.parse parser query))

          hits             (.search searcher query (int max-results))

          highlighter      (make-highlighter query searcher highlight)

          start            (* page results-per-page)

          end              (min (+ start results-per-page)
                                (.totalHits hits))]
      (doall
       (with-meta
         (for [hit (map (partial aget (.scoreDocs hits))
                        (range start end))]
           (document->map
            (.doc ^IndexSearcher searcher
                  (.doc ^ScoreDoc hit))
            (.score ^ScoreDoc hit)
            highlighter))
         {:_total-hits (.totalHits hits)
          :_max-score  (.getMaxScore hits)})))))

(defn search-and-delete
  "Search the supplied index with a query string and then delete all
  of the results."

  ([index query]
   (if *content*
     (search-and-delete index query :_content)
     (throw (Exception. "No default search field specified"))))

  ([index query default-field]
   (let [writer (as-writer index)]
     (let [parser (QueryParser. *version* (as-str default-field) *analyzer*)
           query  (if (= query :all)
                    (MatchAllDocsQuery.)
                    (.parse parser query))
           ^"[Lorg.apache.lucene.search.Query;" arr (into-array [query])]
       (.deleteDocuments ^IndexWriter writer arr)))))
