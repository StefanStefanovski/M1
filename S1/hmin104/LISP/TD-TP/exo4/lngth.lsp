(defun lngth (l)
  (if(equal nil (car l))
      0
    (+ 1 (lngth (cdr l)))))
		
