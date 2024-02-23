import LeanSAT.Reflect.Tactics.CNFDecide

-- https://chat.openai.com/share/4ac95b29-aeff-4e67-98d2-ed16e3dc75a2
set_option trace.profiler true
-- All of these are ~subsecond
example (_ : x = true) (_ : x0 && x1 = x) : x0 = true := by cnf_decide
example (_ : x = true) (_ : x0 && x1 = x) (_ : x10 && x11 = x1) (_ : x00 && x01 = x0) : x00 = true := by cnf_decide
example (_ : x = true) (_ : x0 && x1 = x) (_ : x10 && x11 = x1) (_ : x110 && x111 = x11) (_ : x100 && x101 = x10) (_ : x00 && x01 = x0) (_ : x010 && x011 = x01) (_ : x000 && x001 = x00) : x000 = true := by cnf_decide
example (_ : x = true) (_ : x0 && x1 = x) (_ : x10 && x11 = x1) (_ : x110 && x111 = x11) (_ : x1110 && x1111 = x111) (_ : x1100 && x1101 = x110) (_ : x100 && x101 = x10) (_ : x1010 && x1011 = x101) (_ : x1000 && x1001 = x100) (_ : x00 && x01 = x0) (_ : x010 && x011 = x01) (_ : x0110 && x0111 = x011) (_ : x0100 && x0101 = x010) (_ : x000 && x001 = x00) (_ : x0010 && x0011 = x001) (_ : x0000 && x0001 = x000) : x0000 = true := by cnf_decide

-- TODO: Figure out where recDepth is being spent
-- these are ~2.5s, ~10s
example (_ : x = true) (_ : x0 && x1 = x) (_ : x10 && x11 = x1) (_ : x110 && x111 = x11) (_ : x1110 && x1111 = x111) (_ : x11110 && x11111 = x1111) (_ : x11100 && x11101 = x1110) (_ : x1100 && x1101 = x110) (_ : x11010 && x11011 = x1101) (_ : x11000 && x11001 = x1100) (_ : x100 && x101 = x10) (_ : x1010 && x1011 = x101) (_ : x10110 && x10111 = x1011) (_ : x10100 && x10101 = x1010) (_ : x1000 && x1001 = x100) (_ : x10010 && x10011 = x1001) (_ : x10000 && x10001 = x1000) (_ : x00 && x01 = x0) (_ : x010 && x011 = x01) (_ : x0110 && x0111 = x011) (_ : x01110 && x01111 = x0111) (_ : x01100 && x01101 = x0110) (_ : x0100 && x0101 = x010) (_ : x01010 && x01011 = x0101) (_ : x01000 && x01001 = x0100) (_ : x000 && x001 = x00) (_ : x0010 && x0011 = x001) (_ : x00110 && x00111 = x0011) (_ : x00100 && x00101 = x0010) (_ : x0000 && x0001 = x000) (_ : x00010 && x00011 = x0001) (_ : x00000 && x00001 = x0000) : x00000 = true := by cnf_decide
example (_ : x = true) (_ : x0 && x1 = x) (_ : x10 && x11 = x1) (_ : x110 && x111 = x11) (_ : x1110 && x1111 = x111) (_ : x11110 && x11111 = x1111) (_ : x111110 && x111111 = x11111) (_ : x111100 && x111101 = x11110) (_ : x11100 && x11101 = x1110) (_ : x111010 && x111011 = x11101) (_ : x111000 && x111001 = x11100) (_ : x1100 && x1101 = x110) (_ : x11010 && x11011 = x1101) (_ : x110110 && x110111 = x11011) (_ : x110100 && x110101 = x11010) (_ : x11000 && x11001 = x1100) (_ : x110010 && x110011 = x11001) (_ : x110000 && x110001 = x11000) (_ : x100 && x101 = x10) (_ : x1010 && x1011 = x101) (_ : x10110 && x10111 = x1011) (_ : x101110 && x101111 = x10111) (_ : x101100 && x101101 = x10110) (_ : x10100 && x10101 = x1010) (_ : x101010 && x101011 = x10101) (_ : x101000 && x101001 = x10100) (_ : x1000 && x1001 = x100) (_ : x10010 && x10011 = x1001) (_ : x100110 && x100111 = x10011) (_ : x100100 && x100101 = x10010) (_ : x10000 && x10001 = x1000) (_ : x100010 && x100011 = x10001) (_ : x100000 && x100001 = x10000) (_ : x00 && x01 = x0) (_ : x010 && x011 = x01) (_ : x0110 && x0111 = x011) (_ : x01110 && x01111 = x0111) (_ : x011110 && x011111 = x01111) (_ : x011100 && x011101 = x01110) (_ : x01100 && x01101 = x0110) (_ : x011010 && x011011 = x01101) (_ : x011000 && x011001 = x01100) (_ : x0100 && x0101 = x010) (_ : x01010 && x01011 = x0101) (_ : x010110 && x010111 = x01011) (_ : x010100 && x010101 = x01010) (_ : x01000 && x01001 = x0100) (_ : x010010 && x010011 = x01001) (_ : x010000 && x010001 = x01000) (_ : x000 && x001 = x00) (_ : x0010 && x0011 = x001) (_ : x00110 && x00111 = x0011) (_ : x001110 && x001111 = x00111) (_ : x001100 && x001101 = x00110) (_ : x00100 && x00101 = x0010) (_ : x001010 && x001011 = x00101) (_ : x001000 && x001001 = x00100) (_ : x0000 && x0001 = x000) (_ : x00010 && x00011 = x0001) (_ : x000110 && x000111 = x00011) (_ : x000100 && x000101 = x00010) (_ : x00000 && x00001 = x0000) (_ : x000010 && x000011 = x00001) (_ : x000000 && x000001 = x00000) : x000000 = true := by cnf_decide
-- Greater examples require increased heartbeats and large amounts of memory
--example (_ : x = true) (_ : x0 && x1 = x) (_ : x10 && x11 = x1) (_ : x110 && x111 = x11) (_ : x1110 && x1111 = x111) (_ : x11110 && x11111 = x1111) (_ : x111110 && x111111 = x11111) (_ : x1111110 && x1111111 = x111111) (_ : x1111100 && x1111101 = x111110) (_ : x111100 && x111101 = x11110) (_ : x1111010 && x1111011 = x111101) (_ : x1111000 && x1111001 = x111100) (_ : x11100 && x11101 = x1110) (_ : x111010 && x111011 = x11101) (_ : x1110110 && x1110111 = x111011) (_ : x1110100 && x1110101 = x111010) (_ : x111000 && x111001 = x11100) (_ : x1110010 && x1110011 = x111001) (_ : x1110000 && x1110001 = x111000) (_ : x1100 && x1101 = x110) (_ : x11010 && x11011 = x1101) (_ : x110110 && x110111 = x11011) (_ : x1101110 && x1101111 = x110111) (_ : x1101100 && x1101101 = x110110) (_ : x110100 && x110101 = x11010) (_ : x1101010 && x1101011 = x110101) (_ : x1101000 && x1101001 = x110100) (_ : x11000 && x11001 = x1100) (_ : x110010 && x110011 = x11001) (_ : x1100110 && x1100111 = x110011) (_ : x1100100 && x1100101 = x110010) (_ : x110000 && x110001 = x11000) (_ : x1100010 && x1100011 = x110001) (_ : x1100000 && x1100001 = x110000) (_ : x100 && x101 = x10) (_ : x1010 && x1011 = x101) (_ : x10110 && x10111 = x1011) (_ : x101110 && x101111 = x10111) (_ : x1011110 && x1011111 = x101111) (_ : x1011100 && x1011101 = x101110) (_ : x101100 && x101101 = x10110) (_ : x1011010 && x1011011 = x101101) (_ : x1011000 && x1011001 = x101100) (_ : x10100 && x10101 = x1010) (_ : x101010 && x101011 = x10101) (_ : x1010110 && x1010111 = x101011) (_ : x1010100 && x1010101 = x101010) (_ : x101000 && x101001 = x10100) (_ : x1010010 && x1010011 = x101001) (_ : x1010000 && x1010001 = x101000) (_ : x1000 && x1001 = x100) (_ : x10010 && x10011 = x1001) (_ : x100110 && x100111 = x10011) (_ : x1001110 && x1001111 = x100111) (_ : x1001100 && x1001101 = x100110) (_ : x100100 && x100101 = x10010) (_ : x1001010 && x1001011 = x100101) (_ : x1001000 && x1001001 = x100100) (_ : x10000 && x10001 = x1000) (_ : x100010 && x100011 = x10001) (_ : x1000110 && x1000111 = x100011) (_ : x1000100 && x1000101 = x100010) (_ : x100000 && x100001 = x10000) (_ : x1000010 && x1000011 = x100001) (_ : x1000000 && x1000001 = x100000) (_ : x00 && x01 = x0) (_ : x010 && x011 = x01) (_ : x0110 && x0111 = x011) (_ : x01110 && x01111 = x0111) (_ : x011110 && x011111 = x01111) (_ : x0111110 && x0111111 = x011111) (_ : x0111100 && x0111101 = x011110) (_ : x011100 && x011101 = x01110) (_ : x0111010 && x0111011 = x011101) (_ : x0111000 && x0111001 = x011100) (_ : x01100 && x01101 = x0110) (_ : x011010 && x011011 = x01101) (_ : x0110110 && x0110111 = x011011) (_ : x0110100 && x0110101 = x011010) (_ : x011000 && x011001 = x01100) (_ : x0110010 && x0110011 = x011001) (_ : x0110000 && x0110001 = x011000) (_ : x0100 && x0101 = x010) (_ : x01010 && x01011 = x0101) (_ : x010110 && x010111 = x01011) (_ : x0101110 && x0101111 = x010111) (_ : x0101100 && x0101101 = x010110) (_ : x010100 && x010101 = x01010) (_ : x0101010 && x0101011 = x010101) (_ : x0101000 && x0101001 = x010100) (_ : x01000 && x01001 = x0100) (_ : x010010 && x010011 = x01001) (_ : x0100110 && x0100111 = x010011) (_ : x0100100 && x0100101 = x010010) (_ : x010000 && x010001 = x01000) (_ : x0100010 && x0100011 = x010001) (_ : x0100000 && x0100001 = x010000) (_ : x000 && x001 = x00) (_ : x0010 && x0011 = x001) (_ : x00110 && x00111 = x0011) (_ : x001110 && x001111 = x00111) (_ : x0011110 && x0011111 = x001111) (_ : x0011100 && x0011101 = x001110) (_ : x001100 && x001101 = x00110) (_ : x0011010 && x0011011 = x001101) (_ : x0011000 && x0011001 = x001100) (_ : x00100 && x00101 = x0010) (_ : x001010 && x001011 = x00101) (_ : x0010110 && x0010111 = x001011) (_ : x0010100 && x0010101 = x001010) (_ : x001000 && x001001 = x00100) (_ : x0010010 && x0010011 = x001001) (_ : x0010000 && x0010001 = x001000) (_ : x0000 && x0001 = x000) (_ : x00010 && x00011 = x0001) (_ : x000110 && x000111 = x00011) (_ : x0001110 && x0001111 = x000111) (_ : x0001100 && x0001101 = x000110) (_ : x000100 && x000101 = x00010) (_ : x0001010 && x0001011 = x000101) (_ : x0001000 && x0001001 = x000100) (_ : x00000 && x00001 = x0000) (_ : x000010 && x000011 = x00001) (_ : x0000110 && x0000111 = x000011) (_ : x0000100 && x0000101 = x000010) (_ : x000000 && x000001 = x00000) (_ : x0000010 && x0000011 = x000001) (_ : x0000000 && x0000001 = x000000) : x0000000 = true := by cnf_decide