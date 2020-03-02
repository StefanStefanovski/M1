(defun mysize(tree)
  (+ 1
     (if(consp(car tree))
	 (mysize(car tree))
       (if(car tree) 1 0))
     (if(consp(cdr tree))
	 (mysize(cdr tree))
       (if(cdr tree) 1 0)
       )))
