#include <sys/mman.h>
#include <iostream>
#include <vector>

typedef long long (*vt)();

int main() {
  void * p = mmap(0, 1024, 
    PROT_EXEC | PROT_READ | PROT_WRITE,
    MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
  auto p1 = (u_char*) p;
  auto arr = std::vector<u_char> { 0x48, 0xb8,1,0,0,0,0,0,0,0,0xc3} ;
  for(auto i : arr){
    *p1 = i;
    p1++;
  }
  auto i = ((vt)p)();
  std::cout << i << std::endl;
}