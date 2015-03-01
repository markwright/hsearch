(declaim (optimize (speed 0) (safety 3) (debug 3)))
;; (declaim (optimize (speed 3) (safety 0) (debug 0)))
;; (declaim (optimize (speed 3) (safety 1)))

(require :printv)
(require :sb-sprof)

(defun pprint-array-2d (array)
  (loop for i below (array-total-size array) do
    (if (zerop (mod i (array-dimension array 0)))
      (terpri)
      (princ #\Space))
    (princ (row-major-aref array i))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; IO utility functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun read-ints (string setter)
  (labels ((ri (pos i)
             (multiple-value-bind (x p) (parse-integer string :start pos :junk-allowed t)
               (or (not x)
                   (progn
                     (funcall setter i x))
                   (ri p (1+ i))))))
    (ri 0 0)))

(defun read-line-integer (input-stream)
  (let ((line (read-line input-stream)))
    (parse-integer line :junk-allowed t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mvdo-rebind-gen (rebinds)
  (cond ((null rebinds) nil)
        ((< (length (car rebinds)) 3)
         (mvdo-rebind-gen (cdr rebinds)))
        (t
         (cons (list (if (atom (caar rebinds))
                          'setq
                          'multiple-value-setq)
                      (caar rebinds)
                      (third (car rebinds)))
                (mvdo-rebind-gen (cdr rebinds))))))

(defun mvdo-gen (binds rebinds test body)
  (if (null binds)
      (let ((label (gensym)))
        `(prog nil
          ,label
          (if ,(car test)
              (return (progn ,@ (cdr test))))
          ,@body
          ,@ (mvdo-rebind-gen rebinds)
          (go ,label)))
      (let ((rec (mvdo-gen (cdr binds) rebinds test body)))
        (let ((var/s (caar binds)) (expr (cadar binds)))
          (if (atom var/s)
              `(let ((,var/s ,expr)) ,rec)
              `(multiple-value-bind ,var/s ,expr ,rec))))))

;; on lisp fig.11.10 p.159
(defmacro mvdo* (parm-cl test-cl &body body)
  (mvdo-gen parm-cl parm-cl test-cl body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; linear probing hash table (open addessing with linear probing)
;; linear-hash-table-remove fails if the user has not specified the
;; linear-hash-table-sentinel object, which should only be done once per
;; linear-hash-table.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct (linear-hash-table (:type vector)
                              :named
                              (:constructor make-linear-hash-table
                                  (&key
                                     (test #'=)
                                     (hash #'sxhash)
                                     (initial-size 16)
                                     (sentinel nil)
                                     (v (make-array initial-size))
                                     (n 0))))
  (v (make-array initial-size) :type vector)
  (n 0 :type fixnum)
  (sentinel nil)
  (test #'=)
  (hash #'sxhash))

(defun linear-hash-table-find (h x)
  (let ((t-len (array-dimension (linear-hash-table-v h) 0)))
    (mvdo* (((quotient i) (truncate (funcall (linear-hash-table-hash h) x) t-len) (truncate (1+ i) t-len)))
           ((null (svref (linear-hash-table-v h) i)) nil)
           (when (and (not (eql (svref (linear-hash-table-v h) i) (linear-hash-table-sentinel h)))
                      (funcall (linear-hash-table-test h) x (svref (linear-hash-table-v h) i)))
             (return-from linear-hash-table-find (svref (linear-hash-table-v h) i))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; heap
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct (heap (:type vector)
                 :named
                 (:constructor make-heap
                     (&key
                        (test #'<=)
                        (key-reader #'identity)
                        (key-writer #'identity)
                        (initial-size 16)
                        (k (make-array initial-size))
                        (v (make-array initial-size))
                        (n 0))))
  (k (make-array initial-size) :type vector)
  (v (make-array initial-size) :type vector)
  (n 0 :type fixnum)
  (test #'<)
  (key-reader #'identity)
  (key-writer #'identity))

;; Adjust for 0-based index:
;; (i + 1)/2 - 1 = (i + 1 - 2)/2 = (i - 1)/2
(declaim (inline heap-parent))
(defun heap-parent (i)
  (multiple-value-bind (q rem) (truncate (1- i) 2)
    (declare (ignore rem))
    q))

;; Adjust for 0-based index:
;; c = (2 * (i + 1)) - 1 = 2i + 2 - 1 = 2i + 1 
(declaim (inline heap-left))
(defun heap-left (i)
  (1+ (* 2 i)))

;; Adjust for 0-based index:
;; 2(i + 1) + 1 - 1 = 2(i + 1)
(declaim (inline heap-right))
(defun heap-right (i)
  (* 2 (1+ i)))

(declaim (inline empty-heap-p))
(defun empty-heap-p (h)
  (= (heap-n h) 0))

(declaim (inline full-heap-p))
(defun full-heap-p (h)
  (= (heap-n h) (array-dimension (heap-k h) 0)))

(defun fix-heap (h i)
  (let ((l (heap-left i))
        (r (heap-right i))
        (x 0))
    (progn
      (if (and (< l (heap-n h))
               (funcall (heap-test h) (svref (heap-k h) l) (svref (heap-k h) i)))
          (setf x l)
          (setf x i))
      (when (and (< r (heap-n h))
                 (funcall (heap-test h) (svref (heap-k h) r) (svref (heap-k h) x)))
        (setf x r))
      (unless (= x i)
        (let ((temp-k (svref (heap-k h) i))
              (temp-v (svref (heap-v h) i)))
          (progn
            (setf (svref (heap-k h) i) (svref (heap-k h) x))
            (setf (svref (heap-k h) x) temp-k)
            (setf (svref (heap-v h) i) (svref (heap-v h) x))
            (setf (svref (heap-v h) x) temp-v)
            (fix-heap h x)))))))

;; hads p.212 William's heap-insertion algorithm
(defun heap-insert (h new-value)
  (when (full-heap-p h)
    (let* ((sn (* 2 (array-dimension (heap-k h) 0)))
           (kn (make-array sn))
           (vn (make-array sn)))
      (dotimes (i (heap-n h))
        (setf (svref kn i) (svref (heap-k h) i))
        (setf (svref vn i) (svref (heap-v h) i)))
      (setf (heap-k h) kn)
      (setf (heap-v h) vn)))
  (setf (heap-n h) (1+ (heap-n h)))
  (let ((j (1- (heap-n h)))
        (new-key (funcall (heap-key-reader h) new-value)))
    (do ((stop nil)
         (i (heap-parent j) (heap-parent j)))
        ((or stop (<= j 0)) new-value)
      (if (funcall (heap-test h) (svref (heap-k h) i) new-key)
          (setf stop t)
          (progn
            (setf (svref (heap-k h) j) (svref (heap-k h) i))
            (setf (svref (heap-v h) j) (svref (heap-v h) i))
            (setf j i))))
    (setf (svref (heap-k h) j) new-key)
    (setf (svref (heap-v h) j) new-value)))

(defun heap-search (h field get-field field-test)
  ;; Linear search through all the values in heap vector to find a value
  ;; with the specified field.  If there are multiple values in the heap that match the
  ;; specified value-test compare with the specified value, then one
  ;; of them is returned.  If no values are found that match, then
  ;; return nil.
  ;; Note that field-test can be testing any field or combination of fields
  ;; in the values of the heap, it may not be the key.
  ;; The field is extracted with the specied get-field function.
  (dotimes (i (heap-n h))
    (let ((v (svref (heap-v h) i)))
      (when (funcall field-test field (funcall get-field v))
        (return-from heap-search v))))
  nil)

(defun heap-extract (h &optional (default nil) (error-if-empty nil))
  (if (empty-heap-p h)
      (if (not error-if-empty)
          (return-from heap-extract default)
          (error "heap-extract empty heap"))
      (let ((v (svref (heap-v h) 0)))
        (progn
          (setf (svref (heap-k h) 0) (svref (heap-k h) (1- (heap-n h))))
          (setf (svref (heap-v h) 0) (svref (heap-v h) (1- (heap-n h))))
          (setf (heap-n h) (1- (heap-n h)))
          (fix-heap h 0)
          ;; overwrite the values beyond the end of the vectors with nil to avoid
          ;; retaining references to objects beyond the end of the heap
          (setf (svref (heap-k h) (heap-n h)) nil)
          (setf (svref (heap-v h) (heap-n h)) nil)
          v))))

(defun heap-change-key (h i key)
  (when (or (< i 0) (>= i (heap-n h)))
    (error "heap-change-key i out of range"))
  (let ((value (svref (heap-v h) i)))
    (progn
      (setf (svref (heap-k h) i) key)
      (funcall (heap-key-writer h) value key)
      (setf (svref (heap-v h) i) value)
      (fix-heap h i))))

(defun build-heap (h)
  (multiple-value-bind (s rem) (truncate (heap-n h) 2)
    (declare (ignore rem))
    (do ((i (1- s) (1- i)))
        ((< i 0))
      (fix-heap h i))))

(defun heap-sort (a)
  (let* ((n (array-dimension a 0))
         (h (make-heap :initial-size n :v a :n n)))
    (progn
      (dotimes (i n)
        (setf (svref (heap-k h) i) (funcall (heap-key-reader h) (svref (heap-v h) i))))
      (build-heap h)
      (do ((i (1- n) (1- i)))
          ((< i 1) (heap-k h))
        (let ((temp-k (svref (heap-k h) 0))
              (temp-v (svref (heap-v h) 0)))
          (progn
            (setf (svref (heap-k h) 0) (svref (heap-k h) i))
            (setf (svref (heap-k h) i) temp-k)
            (setf (svref (heap-v h) 0) (svref (heap-v h) i))
            (setf (svref (heap-v h) i) temp-v)
            (setf (heap-n h) (1- (heap-n h)))
            (fix-heap h 0)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; n-puzzle
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *sample-input-string-00*
  "3
0
3
8
4
1
7
2
6
5
"
)

(defparameter *input-string* *sample-input-string-00*)
(defparameter *input-stream* (make-string-input-stream *input-string*))

(defun make-goal (m n)
  (let ((state (make-array (list m n))))
    (progn
      (dotimes (i m)
        (dotimes (j n)
          (setf (aref state i j) (+ (* n i) j))))
      state)))

(defun make-classic-goal (m n)
  (let ((state (make-array (list m n))))
    (progn
      (dotimes (i m)
        (dotimes (j n)
          (setf (aref state i j) (+ (* n i) j 1))))
      (setf (aref state (1- m) (1- n)) 0)
      state)))

(defun copy-array-2d (array)
  (let* ((m (array-dimension array 0))
         (n (array-dimension array 1))
         (new-array (make-array (list m n))))
    (progn
      (dotimes (i m)
        (dotimes (j n)
          (setf (aref new-array i j) (aref array i j))))
      new-array)))

(defun array-2d-to-list (array)
  (let ((m (array-dimension array 0))
        (n (array-dimension array 1))
        (ss nil))
    (progn
      (dotimes (i m)
        (dotimes (j n)
          (setf ss (cons (aref array i j) ss))))
      (reverse ss))))

(defun array-2d-to-list-hack (array)
  (let ((m (array-dimension array 0))
        (n (array-dimension array 1))
        (ss nil))
    (progn
      (dotimes (i m)
        (dotimes (j n)
          (print (aref array i j))))
      (reverse ss))))

(defun move-hole-left (state i j)
  (let ((new-state (copy-array-2d state)))
    (progn
      (setf (aref new-state i (1- j)) (aref state i j))
      (setf (aref new-state i j) (aref state i (1- j)))
      new-state)))

(defun move-hole-right (state i j)
  (let ((new-state (copy-array-2d state)))
    (progn
      (setf (aref new-state i (1+ j)) (aref state i j))
      (setf (aref new-state i j) (aref state i (1+ j)))
      new-state)))

(defun move-hole-up (state i j)
  (let ((new-state (copy-array-2d state)))
    (progn
      (setf (aref new-state (1- i) j) (aref state i j))
      (setf (aref new-state i j) (aref state (1- i) j))
      new-state)))

(defun move-hole-down (state i j)
  (let ((new-state (copy-array-2d state)))
    (progn
      (setf (aref new-state (1+ i) j) (aref state i j))
      (setf (aref new-state i j) (aref state (1+ i) j))
      new-state)))

(defun hole-coordinates (state)
  (dotimes (i (array-dimension state 0))
    (dotimes (j (array-dimension state 1))
      (when (= (aref state i j) 0)
        (return-from hole-coordinates (values i j))))))

(defun n-puzzle-successors (state)
   (multiple-value-bind (i j) (hole-coordinates state)
     (let ((ss nil)
           (m (array-dimension state 0))
           (n (array-dimension state 1)))
       (when (< i (1- m)) (setf ss (cons (move-hole-down state i j) ss)))
       (when (< j (1- n)) (setf ss (cons (move-hole-right state i j) ss)))
       (when (> i 0) (setf ss (cons (move-hole-up state i j) ss)))
       (when (> j 0) (setf ss (cons (move-hole-left state i j) ss)))
       ss)))

;; (defun n-puzzle-cost-fn)

(defconstant +no-move+ 0)
(defconstant +up+ 1)
(defconstant +right+ 2)
(defconstant +down+ 3)
(defconstant +left+ 4)

;; (move +no-move+ :type fixnum)  ;; the move from the parent node to the current node

(defun np-h-no-tiles-out-of-place (goal-state)
  #'(lambda (state)
       (let ((n-tiles-out-of-place 0))
         (dotimes (i (array-dimension goal-state 0))
           (dotimes (j (array-dimension goal-state 1))
             (let ((gij (aref goal-state i j)))
               (unless (or (= gij 0) (= gij (aref state i j)))
                 (setf n-tiles-out-of-place (1+ n-tiles-out-of-place))))))
         n-tiles-out-of-place)))

(defun np-goal-p (goal-state)
  #'(lambda (state)
      (= 0 (funcall (np-h-no-tiles-out-of-place goal-state) state))))

(defun np-w (u v)
  ;; estimate the incremental cost from the node u to node v as 1
  (declare (ignore u v))
  1)

(defun np-h-manhattan-distance (goal-state)
  #'(lambda (state)
      (let* ((m (array-dimension goal-state 0))
             (n (array-dimension goal-state 1))
             (goal-tile-position-vector (make-array (* m n)))
             (h 0))
        (dotimes (i m)
          (dotimes (j n)
            (setf (svref goal-tile-position-vector (aref goal-state i j)) (cons i j))))
        (dotimes (i m)
          (dotimes (j n)
            (let ((tile-no (aref state i j)))
              (unless (= tile-no 0)
                (let* ((goal-tile-pos (svref goal-tile-position-vector tile-no))
                       (goal-tile-x (car goal-tile-pos))
                       (goal-tile-y (cdr goal-tile-pos))
                       (distance (+ (abs (- goal-tile-x i)) (abs (- goal-tile-y j)))))
                  (setf h (+ h distance)))))))
        h)))

(defun np-h-manhattan-distance-linear-conflict (goal-state)
  #'(lambda (state)
      (let* ((m (array-dimension goal-state 0))
             (n (array-dimension goal-state 1))
             (goal-tile-position-vector (make-array (* m n)))
             (h 0)
             (lc 0))
        (dotimes (i m)
          (dotimes (j n)
            (setf (svref goal-tile-position-vector (aref goal-state i j)) (cons i j))))
        (dotimes (i m)
          (dotimes (j n)
            (let ((tile-no (aref state i j)))
              (unless (= tile-no 0)
                (let* ((goal-tile-pos (svref goal-tile-position-vector tile-no))
                       (goal-tile-i (car goal-tile-pos))
                       (goal-tile-j (cdr goal-tile-pos))
                       (distance (+ (abs (- goal-tile-i i)) (abs (- goal-tile-j j))))
                       (signum-diff-goal-tile-i-i (signum (- goal-tile-i i)))
                       (signum-diff-goal-tile-j-j (signum (- goal-tile-j j))))
                  (setf h (+ h distance))
                  (when (= i goal-tile-i)
                    (do ((k (1+ j) (1+ k)))
                        ((>= k n))
                      (let ((suc-tile-no (aref state i k)))
                        (unless (= suc-tile-no 0)
                          (let* ((goal-suc-tile-pos (svref goal-tile-position-vector suc-tile-no))
                                 (goal-suc-tile-i (car goal-suc-tile-pos))
                                 (goal-suc-tile-k (cdr goal-suc-tile-pos)))
                            (when (and (= i goal-suc-tile-i) (/= signum-diff-goal-tile-j-j (- goal-suc-tile-k k)))
                              (setf lc (+ lc 2))))))))
                  (when (= j goal-tile-j)
                    (do ((k (1+ i) (1+ k)))
                        ((>= k m))
                      (let ((suc-tile-no (aref state k j)))
                        (unless (= suc-tile-no 0)
                          (let* ((goal-suc-tile-pos (svref goal-tile-position-vector suc-tile-no))
                                 (goal-suc-tile-k (car goal-suc-tile-pos))
                                 (goal-suc-tile-j (cdr goal-suc-tile-pos)))
                            (when (and (= j goal-suc-tile-j) (/= signum-diff-goal-tile-i-i (- goal-suc-tile-k k)))
                              (setf lc (+ lc 2))))))))
                  )))))
        (+ h lc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Search a binary tree for an integer. A very simple test from section 6.4 of
;; PAIP.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun binary-tree-successors (x) (list (* 2 x) (1+ (* 2 x))))

(defun binary-tree-goal-p (value)
  #'(lambda (x) (eql x value)))

(defun binary-tree-w (u v)
  ;; estimate the incremental cost from the node u to node v as 1
  (declare (ignore u v))
  1)

(defun binary-tree-h (value)
  #'(lambda (x)
      (let ((h (- value x)))
        (if (>= h 0)
            h
            (* 10000 (- 0 h))))))

(defun zero-h (value)
  (declare (ignore value))
  #'(lambda (x)
      (declare (ignore x))
      0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; heuristic search
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct (node (:type vector)
                 :named)
  (f 0 :type fixnum)             ;; f = g + h
  (g 0 :type fixnum)             ;; cost from start node s to current node
  (parent nil)
  (state nil))

;; (defun node-state-equals (state-equals)
;;   #'(lambda (l r)
;;       (funcall state-equals (node-state l) (node-state r))))
;; Note: had to remove the above function and the a*-search parameter
;; &key (state-equals #'eql)
;; as node-state= must be a global function when calling define-hash-table-test,
;; which means I can not make it general like this and use a hash table.

(defun node-state= (l r)
  (equalp l r))

(defun node-f-writer (n f)
  (setf (node-f n) f))

(defun hash-node-state (s)
  (let* ((m (array-dimension s 0))
         (n (array-dimension s 1))
         (h 0))
    (dotimes (i m)
      (dotimes (j n)
        (setf h (+ h (* (+ (* i m) j) (aref s i j))))))
    h))

;;(define-hash-table-test node-state= hash-node-state)

(defun calculate-path (u)
  ;; return a list of states from the start state to the goal.
  ;; Follow the parent pointers from the goal back to the start state.  cons
  ;; each state visited onto the path list.  The resulting path-list
  ;; is the list of states from the start state to the goal.
  (:printv
   (do* ((v u (node-parent v))
         (path-list nil))
        ((null v) path-list)
     (setf path-list (cons (node-state v) path-list)))))

(defun a*-search (start-state w h expand goal-p &key (state-test #'eq) (state-hash-function #'sxhash))
  ;; start-state - start state
  ;; w cost function from parent node u state to current node v state
  ;; h - heuristic function for estimate of cost from current node v state to goal state
  ;; expand - function to generate the successor nodes from the current node
  ;; goal-p - predicate to test if the given state is the goal
  (let* ((start-node (make-node :f (funcall h start-state)   ;; estimate the cost from the start node to the goal using heuristic (h s)
                                :g 0                 ;; the cost from the start node to the start node is 0
                                :parent nil          ;; the start node has no parent
                                :state start-state))
         (closed-q (make-hash-table :test state-test :hash-function state-hash-function))
         (open-q (make-heap :test #'<= :key-reader #'node-f :key-writer #'node-f-writer :initial-size 16))
         (u (heap-insert open-q start-node)))
    (do ()
        ((empty-heap-p open-q) nil)
      (setf u (heap-extract open-q))
      (setf (gethash (node-state u) closed-q) u) ;; insert u into closed
      (if (funcall goal-p (node-state u))
          (return-from a*-search (calculate-path u))
          (dolist (v-state (funcall expand (node-state u)))
            (let ((v-open-node (heap-search open-q v-state #'node-state #'node-state=))) ;; Search to see if v-state in the open set.
              ;; If v-state is in the open set, then it is on the fringe but not yet expanded
              (if (not (null v-open-node))
                  ;; guv is the cost along the new path from start -> u -> v, gv the cost on the old path start -> v
                  (let ((guv (+ (node-g u) (funcall w (node-state u) v-state)))
                        (gv (node-g v-open-node)))
                    (when (< guv gv)  ;; when the new path start -> u -> v is cheaper than the old path start -> v
                      (setf (node-parent v-open-node) u)
                      (heap-change-key open-q 0 (+ guv (funcall h v-state)))))
                  (multiple-value-bind (v-closed-node v-on-closed) (gethash v-state closed-q)
                    (if (not (null v-on-closed))
                        (let ((guv (+ (node-g u) (funcall w (node-state u) v-state)))
                              (gv (node-g v-closed-node)))
                          (when (< guv gv)  ;; when the new path start -> u -> v is cheaper than the old path start -> v
                            (setf (node-parent v-closed-node) u)
                            (remhash v-state closed-q)
                            (setf (node-f v-closed-node) (+ guv (funcall h v-state)))
                            (heap-insert open-q v-closed-node)))
                        (let* ((guv (+ (node-g u) (funcall w (node-state u) v-state)))
                               (v (make-node :f (+ guv (funcall h v-state)) :g guv :parent u :state v-state)))
                          (heap-insert open-q v)))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun read-puzzle ()
  (let* ((n (read-line-integer *input-stream*))
         (m n)
         (puzzle (make-array (list n n))))
    (progn
      (dotimes (i m)
        (dotimes (j n)
          (let ((x (read-line-integer *input-stream*)))
            (setf (aref puzzle i j) x))))
      puzzle)))

;; (let* ((puzzle (read-puzzle))
;;        (m (array-dimension puzzle 0))
;;        (n (array-dimension puzzle 1))
;;        (goal (make-goal m n)))
;;     (pprint-array-2d puzzle)
;;     (breadth-first-search puzzle (is1 goal) #'n-puzzle-successors))

;; (princ (a*-search 1 #'binary-tree-w (binary-tree-h 6)
;;                   #'binary-tree-successors (binary-tree-goal-p 6)
;;                   :state-test #'= :state-hash-function #'sxhash))

;; (sb-sprof:with-profiling (:report :flat :loop nil)

;; (time
;;   (let* ((puzzle (read-puzzle))
;;          (m (array-dimension puzzle 0))
;;          (n (array-dimension puzzle 1))
;;          (goal (make-goal m n)))
;;     (pprint-array-2d puzzle)
;;     (princ (a*-search puzzle #'np-w (np-h-manhattan-distance-linear-conflict goal)
;;                       #'n-puzzle-successors (np-goal-p goal)
;;                       :state-test #'node-state= :state-hash-function #'hash-node-state))))

;; (a*-search #2A((1 0 2) (3 4 5) (6 7 8)) #'np-w (np-h-manhattan-distance-linear-conflict #2A((0 1 2) (3 4 5) (6 7 8))) #'n-puzzle-successors (np-goal-p #2A((0 1 2) (3 4 5) (6 7 8))) :state-test #'node-state= :state-hash-function #'hash-node-state)

;; (time
;;  (a*-search #2A((0 3 8) (4 1 7) (2 6 5))
;;             #'np-w (np-h-manhattan-distance-linear-conflict #2A((0 1 2) (3 4 5) (6 7 8)))
;;             #'n-puzzle-successors (np-goal-p #2A((0 1 2) (3 4 5) (6 7 8)))
;;             :state-test #'node-state= :state-hash-function #'hash-node-state))

;; (time
;;  (a*-search #2A((0 12 9 13) (15 11 10 14) (3 7 2 5) (4 8 6 1))
;;             #'np-w (np-h-manhattan-distance-linear-conflict #2A((1 2 3 4) (5 6 7 8) (9 10 11 12) (13 14 15 0)))
;;             #'n-puzzle-successors (np-goal-p  #2A((1 2 3 4) (5 6 7 8) (9 10 11 12) (13 14 15 0)))
;;             :state-test #'node-state= :state-hash-function #'hash-node-state))

;; (time
;;  (a*-search #2A((6 4 7) (8 5 0) (3 2 1))
;;             #'np-w (np-h-manhattan-distance-linear-conflict #2A((1 2 3) (4 5 6) (7 8 0)))
;;             #'n-puzzle-successors (np-goal-p #2A((1 2 3) (4 5 6) (7 8 0)))
;;             :state-test #'node-state= :state-hash-function #'hash-node-state))
