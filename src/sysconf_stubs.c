#include <errno.h>
#include <unistd.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/fail.h>

CAMLprim value sysconf_nprocs (value unit)
{
  CAMLparam1 (unit);
  long ret;
#if defined(_SC_NPROCESSORS_ONLN)
  ret = sysconf (_SC_NPROCESSORS_ONLN);
#else
  ret = -1;
#endif
  if (ret == -1){
    caml_failwith ("Sysconf.nprocs : sysconf() system call failed");
  }
  CAMLreturn (Val_int (ret));
}
