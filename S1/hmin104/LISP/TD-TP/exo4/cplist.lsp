(defun cplist(l)
  (if(equal (car l) nil)
      nil
    (cons (car l)(cplist (cdr l)))))
