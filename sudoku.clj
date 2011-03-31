(ns sudoku
  (:use [clojure.string :only [join trim split]]))

(def digits (set (apply str (range 1 10))))
(def rows (vec "ABCDEFGHI"))
(def columns (vec digits))
(def squares (for [c columns r rows] [r c]))
(def unit-list (concat
		(partition 9 squares)
		(partition 9 (for [r rows c columns] [r c]))
		(for [cg (partition 3 columns) rg (partition 3 rows)] (for [c cg r rg] [r c]))))
(def units (into {} (map (fn [sq] (vector sq (filter #(some #{sq} %) unit-list))) squares)))
(def peers (into {} (map (fn [[k v]](vector k (remove #{k} (distinct (apply concat v))))) units)))
(def undetermined-grid (into {} (map #(vector % digits) squares)))

(defn run-tests []
  (assert (= (count squares) 81))
  (assert (= (count unit-list) 27))
  (assert (every? #(= (count %) 3) (vals units)))
  (assert (every? #(= (count %) 20) (vals peers)))
  (assert (= (units [\C \2]) (list '([\A \2] [\B \2] [\C \2] [\D \2] [\E \2] [\F \2] [\G \2] [\H \2] [\I \2])
				   '([\C \1] [\C \2] [\C \3] [\C \4] [\C \5] [\C \6] [\C \7] [\C \8] [\C \9])
				   '([\A \1] [\B \1] [\C \1] [\A \2] [\B \2] [\C \2] [\A \3] [\B \3] [\C \3]))))
  (assert (= (set (peers[\C \2])) (set '([\A \2] [\B \2] [\D \2] [\E \2] [\F \2] [\G \2] [\H \2] [\I \2] [\C \1] [\C \3] [\C \4] [\C \5] [\C \6] [\C \7] [\C \8] [\C \9] [\A \1] [\A \3] [\B \1] [\B \3])))))

(defn reduce-while
  "Like reduce, but reduction stops as soon as it becomes falsy."
  [f start-val coll]
  (loop [val start-val others coll]
    (if-let [one (first others)]
      (when-let [new-val (f val one)]
	(recur new-val (next others)))
      val)))

(declare eliminate)
(defn assign
  "Eliminate all the other digits (except d) from grid and propagate.
    Return grid, except return nil if a contradiction is detected."
  [grid s d]
  (let [other-digits (disj (grid s) d)]
    (reduce-while #(eliminate %1 s %2) grid other-digits)))

(defn eliminate
  "Eliminate d from grid and propagate.
    Return grid, except return nil if a contradiction is detected."
  [grid s d]
  (if ((grid s) d)
    (let [new-grid (update-in grid [s] disj d)
	  remaining-digits (new-grid s)]
      (when (seq remaining-digits)
	(let [peer-propagated (if (= (count remaining-digits) 1)
				(reduce-while #(eliminate %1 %2 (first remaining-digits)) new-grid (peers s))
				new-grid)]
	  (when peer-propagated
	    (reduce-while (fn [g u]
			    (let [squares-with-d (filter #((g %) d) u)]
			      (when (seq squares-with-d)
				(if (= (count squares-with-d) 1)
				  (assign g (first squares-with-d) d)
				  g))))
			  peer-propagated (units s))))))
    grid))

(defn grid-values
  "Convert textual representation of grid into a map of squares to digits with '0' or '.' for empties."
  [grid-str]
  (let [chars (keep #(or (digits %) (#{\. \0} %)) grid-str)]
    (assert (= 81 (count chars)))
    (apply hash-map (interleave squares chars))))

(defn parse-grid
  "Convert textual representation of grid to an actual grid, with a first assignment of unique digits.
    Return nil if a contradiction is detected."
  [grid-str]
  (reduce-while (fn [grid [s d]] (if (digits d) (assign grid s d) grid)) undetermined-grid (grid-values grid-str)))

(defn display
  "Display the grid in 2D. I'm not happy with this implementation, feel free to suggest improvements."
  [grid]
  (let [width (inc (reduce #(max %1 (count %2)) 0 (vals grid)))
	line (join "+" (take 3 (repeat (apply str (take (* width 3) (repeat "-"))))))]
    (doseq [r rows]
      (println (join (for [c columns]
                       (format (str "%-" width "s%s")
                               (join (grid [r c]))
                               (if (#{\3 \6} c) "|" "")))))
      (when (#{\C \F} r) (println line)))))

(defn search
  "Using depth-first search and propagation, try all possible values."
  [grid]
  (when grid
    (let [[most-constrained _ solved] (->> squares
					   (map #(let [dcount (count (grid %))] (vector % dcount (= dcount 1))))
					   (reduce (fn [[m mcount solved-so-far] [s _ _]]
						     (let [dc (count (grid s))
							   ssf (and solved-so-far (= dc 1))]
						       (if (< 1 dc mcount)
							 [s dc ssf]
							 [m mcount ssf])))
						   [nil 10 true]))]
      (if solved
	grid
	(some search (map #(assign grid most-constrained %) (grid most-constrained)))))))

(defn solve [grid-str] (search (parse-grid grid-str)))

(defn solve-all
  "Attempt to solve a sequence of grids. Report results.
    When time-threshold is a number of seconds, display puzzles that take longer."
  [grid-strs name time-threshold]
  (let [time-solve (fn [grid-str]
		     (let [g (parse-grid grid-str)
			   s (System/nanoTime)
			   solution (search g)
			   t (/ (- (System/nanoTime) s) 1e9)]
		       (when (and time-threshold (> t time-threshold))
			 (display (grid-values grid-str))
			 (when solution (display solution))
			 (println t " seconds."))
		       [t solution]))
	results (map time-solve grid-strs)
	times (map first results)
	solved (keep second results)
	N (count grid-strs)]
    (when (> N 1)
      (println "Solved " (count solved) "of" N name "puzzles (avg" (/ (reduce + times) N) "sec (" (/ N (reduce + times)) "Hz), max" (reduce max times) ")"))))

(defn from-file
  "Parse a file into a list of strings, separated by sep."
  [filename sep]
  (split (trim (slurp filename)) (re-pattern (or sep (str \newline)))))

(defn random-puzzle
  "Make a random puzzle with n assignments. Restart on contradictions.
    Note the resulting puzzle is not guaranteed to be solvable, but empirically
    about 99.8% of them are solvable. Some have multiple solutions."
  [n]
  (let [new-puzzle (reduce-while #(assign %1 %2 (rand-nth (vec digits))) undetermined-grid (take (or n 17) (shuffle squares)))]
    (if new-puzzle
      (apply str (map #(let [ds (new-puzzle %)] (if (= (count ds) 1) (str (first ds)) ".")) squares))
      (random-puzzle n))))