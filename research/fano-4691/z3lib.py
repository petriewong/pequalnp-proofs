"""Minimal libz3 C API adapter for the local SMT-LIB experiments."""
import ctypes as C
from ctypes.util import find_library

Z = C.CDLL(find_library('z3') or 'libz3.so.4')
for name, output, inputs in [
    ('mk_config', C.c_void_p, []),
    ('mk_context', C.c_void_p, [C.c_void_p]),
    ('del_config', None, [C.c_void_p]),
    ('del_context', None, [C.c_void_p]),
    ('eval_smtlib2_string', C.c_char_p, [C.c_void_p,C.c_char_p]),
]:
    f = getattr(Z, 'Z3_'+name)
    f.restype, f.argtypes = output, inputs
