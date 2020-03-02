(defun memb (x l)
  (
   if(= x (car l))
	(cdr l)
	(memb x (cdr l))))

