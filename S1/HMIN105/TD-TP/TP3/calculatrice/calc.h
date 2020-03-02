typedef struct calc_msg {
  long mtype;
  char s;
  int x;
  int y;
} calc_msg;

typedef struct eval_msg {
  long mtype;
  int res;
} eval_msg;

