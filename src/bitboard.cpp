/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2023 The Stockfish developers (see AUTHORS file)

  Stockfish is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Stockfish is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <algorithm>
#include <bitset>

#include "bitboard.h"
#include "misc.h"

namespace Stockfish {

uint8_t PopCnt16[1 << 16];
uint8_t SquareDistance[SQUARE_NB][SQUARE_NB];

Bitboard SquareBB[SQUARE_NB];
Bitboard LineBB[SQUARE_NB][SQUARE_NB];
Bitboard BetweenBB[SQUARE_NB][SQUARE_NB];
Bitboard PseudoAttacks[PIECE_TYPE_NB][SQUARE_NB];
Bitboard PawnAttacks[COLOR_NB][SQUARE_NB];

namespace {
  constexpr Bitboard sliding_attack(PieceType pt, Square sq, Bitboard occupied);
  constexpr Bitboard edges(Square sq);
  constexpr std::array<Magic<RookBits>, SQUARE_NB> init_rook_magic();
  constexpr std::array<Magic<BishopBits>, SQUARE_NB> init_bishop_magic();
  template <PieceType pt, unsigned bits>
  constexpr std::array<std::array<Bitboard, (1 << bits)>, SQUARE_NB> init_table(const std::array<Magic<bits>, SQUARE_NB>& magics);
}

std::array<Magic<RookBits>, SQUARE_NB> RookMagics;
std::array<Magic<BishopBits>, SQUARE_NB> BishopMagics;
std::array<std::array<Bitboard, (1 << RookBits)>, SQUARE_NB>   RookAttackTable;
std::array<std::array<Bitboard, (1 << BishopBits)>, SQUARE_NB> BishopAttackTable;

/// safe_destination() returns the bitboard of target square for the given step
/// from the given square. If the step is off the board, returns empty bitboard.

inline Bitboard safe_destination(Square s, int step) {
    Square to = Square(s + step);
    return is_ok(to) && distance(s, to) <= 2 ? square_bb(to) : Bitboard(0);
}


/// Bitboards::pretty() returns an ASCII representation of a bitboard suitable
/// to be printed to standard output. Useful for debugging.

std::string Bitboards::pretty(Bitboard b) {

  std::string s = "+---+---+---+---+---+---+---+---+\n";

  for (Rank r = RANK_8; r >= RANK_1; --r)
  {
      for (File f = FILE_A; f <= FILE_H; ++f)
          s += b & make_square(f, r) ? "| X " : "|   ";

      s += "| " + std::to_string(1 + r) + "\n+---+---+---+---+---+---+---+---+\n";
  }
  s += "  a   b   c   d   e   f   g   h\n";

  return s;
}


/// Bitboards::init() initializes various bitboard tables. It is called at
/// startup and relies on global objects to be already zero-initialized.

void Bitboards::init() {

  for (unsigned i = 0; i < (1 << 16); ++i)
      PopCnt16[i] = uint8_t(std::bitset<16>(i).count());

  for (Square s = SQ_A1; s <= SQ_H8; ++s)
      SquareBB[s] = (1ULL << s);

  for (Square s1 = SQ_A1; s1 <= SQ_H8; ++s1)
      for (Square s2 = SQ_A1; s2 <= SQ_H8; ++s2)
          SquareDistance[s1][s2] = std::max(distance<File>(s1, s2), distance<Rank>(s1, s2));

  BishopMagics = init_bishop_magic();
  RookMagics = init_rook_magic();

  BishopAttackTable = init_table<BISHOP, BishopBits>(BishopMagics);
  RookAttackTable = init_table<ROOK, RookBits>(RookMagics);

  for (Square s1 = SQ_A1; s1 <= SQ_H8; ++s1)
  {
      PawnAttacks[WHITE][s1] = pawn_attacks_bb<WHITE>(square_bb(s1));
      PawnAttacks[BLACK][s1] = pawn_attacks_bb<BLACK>(square_bb(s1));

      for (int step : {-9, -8, -7, -1, 1, 7, 8, 9} )
         PseudoAttacks[KING][s1] |= safe_destination(s1, step);

      for (int step : {-17, -15, -10, -6, 6, 10, 15, 17} )
         PseudoAttacks[KNIGHT][s1] |= safe_destination(s1, step);

      PseudoAttacks[QUEEN][s1]  = PseudoAttacks[BISHOP][s1] = attacks_bb<BISHOP>(s1, 0);
      PseudoAttacks[QUEEN][s1] |= PseudoAttacks[  ROOK][s1] = attacks_bb<  ROOK>(s1, 0);

      for (PieceType pt : { BISHOP, ROOK })
          for (Square s2 = SQ_A1; s2 <= SQ_H8; ++s2)
          {
              if (PseudoAttacks[pt][s1] & s2)
              {
                  LineBB[s1][s2]    = (attacks_bb(pt, s1, 0) & attacks_bb(pt, s2, 0)) | s1 | s2;
                  BetweenBB[s1][s2] = (attacks_bb(pt, s1, square_bb(s2)) & attacks_bb(pt, s2, square_bb(s1)));
              }
              BetweenBB[s1][s2] |= s2;
          }
  }
}

namespace {

  constexpr Bitboard sliding_attack(PieceType pt, Square sq, Bitboard occupied) {

    Bitboard attacks = 0;
    Direction   RookDirections[4] = {NORTH, SOUTH, EAST, WEST};
    Direction BishopDirections[4] = {NORTH_EAST, SOUTH_EAST, SOUTH_WEST, NORTH_WEST};

    for (Direction d : (pt == ROOK ? RookDirections : BishopDirections))
    {
        Square s = sq;
        while (safe_destination(s, d) && !(occupied & s))
            attacks |= (s += d);
    }

    return attacks;
  }

  constexpr Bitboard edges(Square sq)
  {
      return ((Rank1BB | Rank8BB) & ~rank_bb(sq)) | ((FileABB | FileHBB) & ~file_bb(sq));
  }

  constexpr std::array<Magic<RookBits>, SQUARE_NB> init_rook_magic()
  {
      return std::array<Magic<RookBits>, SQUARE_NB> {
              Magic<RookBits>(sliding_attack(ROOK, SQ_A1, 0) & ~edges(SQ_A1), 0x0000002044010082LU), // 0x000
              Magic<RookBits>(sliding_attack(ROOK, SQ_B1, 0) & ~edges(SQ_B1), 0x0000404208010084LU), // 0x040
              Magic<RookBits>(sliding_attack(ROOK, SQ_C1, 0) & ~edges(SQ_C1), 0x0001000820840021LU), // 0x004
              Magic<RookBits>(sliding_attack(ROOK, SQ_D1, 0) & ~edges(SQ_D1), 0x0000080004100201LU), // 0x100
              Magic<RookBits>(sliding_attack(ROOK, SQ_E1, 0) & ~edges(SQ_E1), 0x0001002044100009LU), // 0x001
              Magic<RookBits>(sliding_attack(ROOK, SQ_F1, 0) & ~edges(SQ_F1), 0x0000a50040a00111LU), // 0x002
              Magic<RookBits>(sliding_attack(ROOK, SQ_G1, 0) & ~edges(SQ_G1), 0x00050010a283c001LU), // 0x001
              Magic<RookBits>(sliding_attack(ROOK, SQ_H1, 0) & ~edges(SQ_H1), 0x0013110080244202LU), // 0x000
              Magic<RookBits>(sliding_attack(ROOK, SQ_A2, 0) & ~edges(SQ_A2), 0x00002c0058802600LU), // 0x008
              Magic<RookBits>(sliding_attack(ROOK, SQ_B2, 0) & ~edges(SQ_B2), 0x0001080850022400LU), // 0x006
              Magic<RookBits>(sliding_attack(ROOK, SQ_C2, 0) & ~edges(SQ_C2), 0x0007000400009100LU), // 0x014
              Magic<RookBits>(sliding_attack(ROOK, SQ_D2, 0) & ~edges(SQ_D2), 0x000a001058602200LU), // 0x005
              Magic<RookBits>(sliding_attack(ROOK, SQ_E2, 0) & ~edges(SQ_E2), 0x0008104020040200LU), // 0x104
              Magic<RookBits>(sliding_attack(ROOK, SQ_F2, 0) & ~edges(SQ_F2), 0x0020028044900080LU), // 0x00a
              Magic<RookBits>(sliding_attack(ROOK, SQ_G2, 0) & ~edges(SQ_G2), 0x0040002000100020LU), // 0x101
              Magic<RookBits>(sliding_attack(ROOK, SQ_H2, 0) & ~edges(SQ_H2), 0x00ed8005c2610100LU), // 0x001
              Magic<RookBits>(sliding_attack(ROOK, SQ_A3, 0) & ~edges(SQ_A3), 0x0000330040960004LU), // 0x001
              Magic<RookBits>(sliding_attack(ROOK, SQ_B3, 0) & ~edges(SQ_B3), 0x00025014480c0009LU), // 0x00a
              Magic<RookBits>(sliding_attack(ROOK, SQ_C3, 0) & ~edges(SQ_C3), 0x0004000802010004LU), // 0x201
              Magic<RookBits>(sliding_attack(ROOK, SQ_D3, 0) & ~edges(SQ_D3), 0x0006009001420004LU), // 0x028
              Magic<RookBits>(sliding_attack(ROOK, SQ_E3, 0) & ~edges(SQ_E3), 0x0015002010010002LU), // 0x006
              Magic<RookBits>(sliding_attack(ROOK, SQ_F3, 0) & ~edges(SQ_F3), 0x0020001004001000LU), // 0x280
              Magic<RookBits>(sliding_attack(ROOK, SQ_G3, 0) & ~edges(SQ_G3), 0x000a021100220008LU), // 0x018
              Magic<RookBits>(sliding_attack(ROOK, SQ_H3, 0) & ~edges(SQ_H3), 0x0080004000204010LU), // 0x200
              Magic<RookBits>(sliding_attack(ROOK, SQ_A4, 0) & ~edges(SQ_A4), 0x0001000491000246LU), // 0x001
              Magic<RookBits>(sliding_attack(ROOK, SQ_B4, 0) & ~edges(SQ_B4), 0x0003100a04001658LU), // 0x006
              Magic<RookBits>(sliding_attack(ROOK, SQ_C4, 0) & ~edges(SQ_C4), 0x0000200080200100LU), // 0xc00
              Magic<RookBits>(sliding_attack(ROOK, SQ_D4, 0) & ~edges(SQ_D4), 0x0000402008008004LU), // 0x810
              Magic<RookBits>(sliding_attack(ROOK, SQ_E4, 0) & ~edges(SQ_E4), 0x0004000200100100LU), // 0x408
              Magic<RookBits>(sliding_attack(ROOK, SQ_F4, 0) & ~edges(SQ_F4), 0x0010002000200402LU), // 0x202
              Magic<RookBits>(sliding_attack(ROOK, SQ_G4, 0) & ~edges(SQ_G4), 0x0040000800100010LU), // 0x480
              Magic<RookBits>(sliding_attack(ROOK, SQ_H4, 0) & ~edges(SQ_H4), 0x00b4c003888001a0LU), // 0x001
              Magic<RookBits>(sliding_attack(ROOK, SQ_A5, 0) & ~edges(SQ_A5), 0x0001440200008829LU), // 0x002
              Magic<RookBits>(sliding_attack(ROOK, SQ_B5, 0) & ~edges(SQ_B5), 0x0002000040008001LU), // 0x500
              Magic<RookBits>(sliding_attack(ROOK, SQ_C5, 0) & ~edges(SQ_C5), 0x0002003a00081910LU), // 0x009
              Magic<RookBits>(sliding_attack(ROOK, SQ_D5, 0) & ~edges(SQ_D5), 0x0000200200041001LU), // 0x208
              Magic<RookBits>(sliding_attack(ROOK, SQ_E5, 0) & ~edges(SQ_E5), 0x0010100080080002LU), // 0x042
              Magic<RookBits>(sliding_attack(ROOK, SQ_F5, 0) & ~edges(SQ_F5), 0x0000200020040008LU), // 0x600
              Magic<RookBits>(sliding_attack(ROOK, SQ_G5, 0) & ~edges(SQ_G5), 0x000c400100082480LU), // 0x022
              Magic<RookBits>(sliding_attack(ROOK, SQ_H5, 0) & ~edges(SQ_H5), 0x0080002040004013LU), // 0x200
              Magic<RookBits>(sliding_attack(ROOK, SQ_A6, 0) & ~edges(SQ_A6), 0x0001f2000286224cLU), // 0x008
              Magic<RookBits>(sliding_attack(ROOK, SQ_B6, 0) & ~edges(SQ_B6), 0x0001440010009218LU), // 0x005
              Magic<RookBits>(sliding_attack(ROOK, SQ_C6, 0) & ~edges(SQ_C6), 0x0003e80040200210LU), // 0x00a
              Magic<RookBits>(sliding_attack(ROOK, SQ_D6, 0) & ~edges(SQ_D6), 0x0000010004100800LU), // 0x102
              Magic<RookBits>(sliding_attack(ROOK, SQ_E6, 0) & ~edges(SQ_E6), 0x0008002020040002LU), // 0x900
              Magic<RookBits>(sliding_attack(ROOK, SQ_F6, 0) & ~edges(SQ_F6), 0x0002020008104080LU), // 0x009
              Magic<RookBits>(sliding_attack(ROOK, SQ_G6, 0) & ~edges(SQ_G6), 0x0000404000200008LU), // 0x202
              Magic<RookBits>(sliding_attack(ROOK, SQ_H6, 0) & ~edges(SQ_H6), 0x007a808000400ad2LU), // 0x002
              Magic<RookBits>(sliding_attack(ROOK, SQ_A7, 0) & ~edges(SQ_A7), 0x004200004091040aLU), // 0x001
              Magic<RookBits>(sliding_attack(ROOK, SQ_B7, 0) & ~edges(SQ_B7), 0x0032000041180200LU), // 0x012
              Magic<RookBits>(sliding_attack(ROOK, SQ_C7, 0) & ~edges(SQ_C7), 0x0001000400080100LU), // 0x005
              Magic<RookBits>(sliding_attack(ROOK, SQ_D7, 0) & ~edges(SQ_D7), 0x0001000100040800LU), // 0x012
              Magic<RookBits>(sliding_attack(ROOK, SQ_E7, 0) & ~edges(SQ_E7), 0x0044004010082004LU), // 0x240
              Magic<RookBits>(sliding_attack(ROOK, SQ_F7, 0) & ~edges(SQ_F7), 0x0022001080042040LU), // 0x082
              Magic<RookBits>(sliding_attack(ROOK, SQ_G7, 0) & ~edges(SQ_G7), 0x0032000a00208240LU), // 0x022
              Magic<RookBits>(sliding_attack(ROOK, SQ_H7, 0) & ~edges(SQ_H7), 0x0040800080400010LU), // 0x002
              Magic<RookBits>(sliding_attack(ROOK, SQ_A8, 0) & ~edges(SQ_A8), 0x0200020400288043LU), // 0x000
              Magic<RookBits>(sliding_attack(ROOK, SQ_B8, 0) & ~edges(SQ_B8), 0x040008100402138dLU), // 0x001
              Magic<RookBits>(sliding_attack(ROOK, SQ_C8, 0) & ~edges(SQ_C8), 0x0a004400180a0010LU), // 0x002
              Magic<RookBits>(sliding_attack(ROOK, SQ_D8, 0) & ~edges(SQ_D8), 0x0100048100100800LU), // 0x002
              Magic<RookBits>(sliding_attack(ROOK, SQ_E8, 0) & ~edges(SQ_E8), 0x0900082002100005LU), // 0x080
              Magic<RookBits>(sliding_attack(ROOK, SQ_F8, 0) & ~edges(SQ_F8), 0x0a00100880402004LU), // 0x080
              Magic<RookBits>(sliding_attack(ROOK, SQ_G8, 0) & ~edges(SQ_G8), 0x1100088410400100LU), // 0x004
              Magic<RookBits>(sliding_attack(ROOK, SQ_H8, 0) & ~edges(SQ_H8), 0x0200110200204080LU), // 0x000
      };
  }

  constexpr std::array<Magic<BishopBits>, SQUARE_NB> init_bishop_magic()
  {
      return std::array<Magic<BishopBits>, SQUARE_NB> {
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_A1, 0) & ~edges(SQ_A1), 0x0000500102002008LU), // 0b100100010
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_B1, 0) & ~edges(SQ_B1), 0x0000010101000880LU), // 0b111000010
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_C1, 0) & ~edges(SQ_C1), 0x0000000042008100LU), // 0b101000110
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_D1, 0) & ~edges(SQ_D1), 0x0000000001200404LU), // 0b010111000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_E1, 0) & ~edges(SQ_E1), 0x0000000002008022LU), // 0b011011000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_F1, 0) & ~edges(SQ_F1), 0x0000000201010040LU), // 0b010011010
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_G1, 0) & ~edges(SQ_G1), 0x0000002080080080LU), // 0b101001010
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_H1, 0) & ~edges(SQ_H1), 0x000100080084004cLU), // 0b001010100
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_A2, 0) & ~edges(SQ_A2), 0x0000808100040400LU), // 0b111010000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_B2, 0) & ~edges(SQ_B2), 0x0040100401004200LU), // 0b000001111
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_C2, 0) & ~edges(SQ_C2), 0x0000680208020000LU), // 0b000001111
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_D2, 0) & ~edges(SQ_D2), 0x0000000120020104LU), // 0b001011010
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_E2, 0) & ~edges(SQ_E2), 0x0000000201010028LU), // 0b010010011
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_F2, 0) & ~edges(SQ_F2), 0x000002000a0100a6LU), // 0b010101001
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_G2, 0) & ~edges(SQ_G2), 0x0001001202004000LU), // 0b100011001
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_H2, 0) & ~edges(SQ_H2), 0x00040200840087f1LU), // 0b010010101
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_A3, 0) & ~edges(SQ_A3), 0x0018061012002180LU), // 0b000111001
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_B3, 0) & ~edges(SQ_B3), 0x0008002100400020LU), // 0b110000101
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_C3, 0) & ~edges(SQ_C3), 0x0000a00d40800700LU), // 0b000001001
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_D3, 0) & ~edges(SQ_D3), 0x0000205004000480LU), // 0b000010100
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_E3, 0) & ~edges(SQ_E3), 0x0000002008003020LU), // 0b000101000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_F3, 0) & ~edges(SQ_F3), 0x0000402080424020LU), // 0b011000000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_G3, 0) & ~edges(SQ_G3), 0x0004020044041000LU), // 0b000011011
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_H3, 0) & ~edges(SQ_H3), 0x0004040201000800LU), // 0b100001011
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_A4, 0) & ~edges(SQ_A4), 0x00080e090062000fLU), // 0b001111000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_B4, 0) & ~edges(SQ_B4), 0x0010040080880410LU), // 0b001011100
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_C4, 0) & ~edges(SQ_C4), 0x0000220020040400LU), // 0b100001000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_D4, 0) & ~edges(SQ_D4), 0x0008010040100802LU), // 0b000000000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_E4, 0) & ~edges(SQ_E4), 0x0002010040040040LU), // 0b000000000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_F4, 0) & ~edges(SQ_F4), 0x0000108200401200LU), // 0b010000010
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_G4, 0) & ~edges(SQ_G4), 0x0000820024c80021LU), // 0b110001100
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_H4, 0) & ~edges(SQ_H4), 0x0000100400100080LU), // 0b100101010
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_A5, 0) & ~edges(SQ_A5), 0x0002820001004010LU), // 0b001001101
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_B5, 0) & ~edges(SQ_B5), 0x0000090002008040LU), // 0b100101010
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_C5, 0) & ~edges(SQ_C5), 0x001001000020110eLU), // 0b001000010
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_D5, 0) & ~edges(SQ_D5), 0x0004040030410042LU), // 0b000000000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_E5, 0) & ~edges(SQ_E5), 0x0004010010089080LU), // 0b000000000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_F5, 0) & ~edges(SQ_F5), 0x000c010002040c00LU), // 0b001000010
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_G5, 0) & ~edges(SQ_G5), 0x0000100060020480LU), // 0b001001110
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_H5, 0) & ~edges(SQ_H5), 0x0004010102080108LU), // 0b110000011
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_A6, 0) & ~edges(SQ_A6), 0x0000807810040200LU), // 0b100010110
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_B6, 0) & ~edges(SQ_B6), 0x0000083021040020LU), // 0b110010100
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_C6, 0) & ~edges(SQ_C6), 0x0004020600840100LU), // 0b000010010
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_D6, 0) & ~edges(SQ_D6), 0x0018040040401fc2LU), // 0b001001000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_E6, 0) & ~edges(SQ_E6), 0x003c001801098204LU), // 0b000011000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_F6, 0) & ~edges(SQ_F6), 0x0002042010200820LU), // 0b101000000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_G6, 0) & ~edges(SQ_G6), 0x0001004028010100LU), // 0b100010110
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_H6, 0) & ~edges(SQ_H6), 0x0000804000808100LU), // 0b011010001
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_A7, 0) & ~edges(SQ_A7), 0x0000004010080208LU), // 0b101001010
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_B7, 0) & ~edges(SQ_B7), 0x0000010020820040LU), // 0b110100010
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_C7, 0) & ~edges(SQ_C7), 0x0000020104004000LU), // 0b010001110
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_D7, 0) & ~edges(SQ_D7), 0x0000140101011c72LU), // 0b000110011
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_E7, 0) & ~edges(SQ_E7), 0x0000004400402640LU), // 0b011000101
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_F7, 0) & ~edges(SQ_F7), 0x0000020010108160LU), // 0b110010001
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_G7, 0) & ~edges(SQ_G7), 0x0000010808008002LU), // 0b001010110
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_H7, 0) & ~edges(SQ_H7), 0x0000040808010006LU), // 0b100001110
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_A8, 0) & ~edges(SQ_A8), 0x0002040082002000LU), // 0b001001100
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_B8, 0) & ~edges(SQ_B8), 0x00040080880040f6LU), // 0b010100110
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_C8, 0) & ~edges(SQ_C8), 0x00000800401fc800LU), // 0b001111000
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_D8, 0) & ~edges(SQ_D8), 0x0000808041000000LU), // 0b110010010
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_E8, 0) & ~edges(SQ_E8), 0x0008020004014060LU), // 0b000110101
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_F8, 0) & ~edges(SQ_F8), 0x0030040181041018LU), // 0b000011101
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_G8, 0) & ~edges(SQ_G8), 0x0000202100202100LU), // 0b111000100
              Magic<BishopBits>(sliding_attack(BISHOP, SQ_H8, 0) & ~edges(SQ_H8), 0x0060002200404200LU), // 0b001000110
      };
  }

  // init_magics() computes all rook and bishop attacks at startup. Magic
  // bitboards are used to look up attacks of sliding pieces. As a reference see
  // www.chessprogramming.org/Magic_Bitboards. In particular, here we use the so
  // called "fancy" approach.

  template <PieceType pt, unsigned bits>
  constexpr std::array<std::array<Bitboard, (1 << bits)>, SQUARE_NB> init_table(const std::array<Magic<bits>, SQUARE_NB>& magics)
  {
      std::array<std::array<Bitboard, (1 << bits)>, SQUARE_NB> table{};
      std::array<bool, (1 << bits)> occured{};
      for (Square s = SQ_A1; s <= SQ_H8; ++s)
      {
          occured.fill(false);
          const Magic<bits> magic = magics[s];
          Bitboard board = 0;
          do {
              unsigned idx = magic.index(board);
              assert(idx < (1 << bits));
              assert(occured[idx] == false);
              occured[idx] = true;
              table[s][idx] = sliding_attack(pt, s, board);
              board = (board - magic.mask) & magic.mask;
          } while (board);
      }
      return table;
  }

  /*
  void init_magics(PieceType pt, Bitboard table[], Magic magics[]) {

    #ifndef USE_PEXT
    // Optimal PRNG seeds to pick the correct magics in the shortest time
    int seeds[][RANK_NB] = { { 8977, 44560, 54343, 38998,  5731, 95205, 104912, 17020 },
                             {  728, 10316, 55013, 32803, 12281, 15100,  16645,   255 } };
    int epoch[4096] = {}, cnt = 0;
    Bitboard occupancy[4096], reference[4096];
    #endif

    Bitboard edges, b;
    int size = 0;

    for (Square s = SQ_A1; s <= SQ_H8; ++s)
    {
        // Board edges are not considered in the relevant occupancies
        edges = ((Rank1BB | Rank8BB) & ~rank_bb(s)) | ((FileABB | FileHBB) & ~file_bb(s));

        // Given a square 's', the mask is the bitboard of sliding attacks from
        // 's' computed on an empty board. The index must be big enough to contain
        // all the attacks for each possible subset of the mask and so is 2 power
        // the number of 1s of the mask. Hence we deduce the size of the shift to
        // apply to the 64 or 32 bits word to get the index.
        Magic& m = magics[s];
        m.mask  = sliding_attack(pt, s, 0) & ~edges;
        #ifndef USE_PEXT
            m.shift = ArchBits - popcount(m.mask);
        #endif
        // Set the offset for the attacks table of the square. We have individual
        // table sizes for each square with "Fancy Magic Bitboards".
        m.attacks = s == SQ_A1 ? table : magics[s - 1].attacks + size;

        // Use Carry-Rippler trick to enumerate all subsets of masks[s] and
        // store the corresponding sliding attack bitboard in reference[].
        b = size = 0;
        do {
            #ifdef USE_PEXT
                m.attacks[pext(b, m.mask)] = sliding_attack(pt, s, b);
            #else
                occupancy[size] = b;
                reference[size] = sliding_attack(pt, s, b);
            #endif
            size++;
            b = (b - m.mask) & m.mask;
        } while (b);

        #ifndef USE_PEXT
            PRNG rng(seeds[ArchBits == 64][rank_of(s)]);

            // Find a magic for square 's' picking up an (almost) random number
            // until we find the one that passes the verification test.
            for (int i = 0; i < size; )
            {
                for (m.magic = 0; popcount((m.magic * m.mask) >> 56) < 6; )
                    m.magic = rng.sparse_rand<Bitboard>();

                // A good magic must map every possible occupancy to an index that
                // looks up the correct sliding attack in the attacks[s] database.
                // Note that we build up the database for square 's' as a side
                // effect of verifying the magic. Keep track of the attempt count
                // and save it in epoch[], little speed-up trick to avoid resetting
                // m.attacks[] after every failed attempt.
                for (++cnt, i = 0; i < size; ++i)
                {
                    unsigned idx = m.index(occupancy[i]);

                    if (epoch[idx] < cnt)
                    {
                        epoch[idx] = cnt;
                        m.attacks[idx] = reference[i];
                    }
                    else if (m.attacks[idx] != reference[i])
                        break;
                }
            }
        #endif
    }
  }
   */
}

} // namespace Stockfish
