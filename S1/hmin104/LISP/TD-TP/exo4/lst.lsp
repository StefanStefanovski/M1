(defun lst (l)
  (if(equal (cdr l) nil)
      (car l)
      (lst (cdr l))))
