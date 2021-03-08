int f(bool a, bool b,  bool c) {
  if (a && b && c || (a && !b)) { return 12312; }
  else { return 323; }
}

int f1(int a, int b) { 
  return (a >= b);
}