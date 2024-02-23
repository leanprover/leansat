import LeanSAT.Reflect.Tactics.CNFDecide

-- https://chat.openai.com/share/4ac95b29-aeff-4e67-98d2-ed16e3dc75a2
set_option profiler true
-- Currently takes 0.8s, 2.5s, 8s, 30s, and blows up with a max rec depth error. (On Scott's machine.)
example (_ : x = true) (_ : x0 && x1 = x) : x0 = true := by cnf_decide
example (_ : x = true) (_ : x0 && x1 = x) (_ : x10 && x11 = x1) (_ : x00 && x01 = x0) : x00 = true := by cnf_decide
example (_ : x = true) (_ : x0 && x1 = x) (_ : x10 && x11 = x1) (_ : x110 && x111 = x11) (_ : x100 && x101 = x10) (_ : x00 && x01 = x0) (_ : x010 && x011 = x01) (_ : x000 && x001 = x00) : x000 = true := by cnf_decide
example (_ : x = true) (_ : x0 && x1 = x) (_ : x10 && x11 = x1) (_ : x110 && x111 = x11) (_ : x1110 && x1111 = x111) (_ : x1100 && x1101 = x110) (_ : x100 && x101 = x10) (_ : x1010 && x1011 = x101) (_ : x1000 && x1001 = x100) (_ : x00 && x01 = x0) (_ : x010 && x011 = x01) (_ : x0110 && x0111 = x011) (_ : x0100 && x0101 = x010) (_ : x000 && x001 = x00) (_ : x0010 && x0011 = x001) (_ : x0000 && x0001 = x000) : x0000 = true := by cnf_decide

-- TODO: Figure out where recDepth is being spent
set_option maxRecDepth 1000000
example (_ : x = true) (_ : x0 && x1 = x) (_ : x10 && x11 = x1) (_ : x110 && x111 = x11) (_ : x1110 && x1111 = x111) (_ : x11110 && x11111 = x1111) (_ : x11100 && x11101 = x1110) (_ : x1100 && x1101 = x110) (_ : x11010 && x11011 = x1101) (_ : x11000 && x11001 = x1100) (_ : x100 && x101 = x10) (_ : x1010 && x1011 = x101) (_ : x10110 && x10111 = x1011) (_ : x10100 && x10101 = x1010) (_ : x1000 && x1001 = x100) (_ : x10010 && x10011 = x1001) (_ : x10000 && x10001 = x1000) (_ : x00 && x01 = x0) (_ : x010 && x011 = x01) (_ : x0110 && x0111 = x011) (_ : x01110 && x01111 = x0111) (_ : x01100 && x01101 = x0110) (_ : x0100 && x0101 = x010) (_ : x01010 && x01011 = x0101) (_ : x01000 && x01001 = x0100) (_ : x000 && x001 = x00) (_ : x0010 && x0011 = x001) (_ : x00110 && x00111 = x0011) (_ : x00100 && x00101 = x0010) (_ : x0000 && x0001 = x000) (_ : x00010 && x00011 = x0001) (_ : x00000 && x00001 = x0000) : x00000 = true := by cnf_decide
