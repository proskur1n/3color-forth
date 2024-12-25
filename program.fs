#! /bin/env -S gforth -e bye

%001 constant CRED
%010 constant CGREEN
%100 constant CBLUE

: allot-init ( u c -- )
  here -rot over allot fill
;

: swap-cells ( addr1 addr2 -- )
  dup @ >r over @ swap ! r> swap !
;

: swap-array-elements ( offset1 offset2 baseaddr -- )
  >r cells r@ + swap cells r> + swap-cells
;

: parse-number ( "number" -- n err )
  parse-name s>number? 0= or
;

: parse-nonnegative ( "number" -- n )
  parse-number over 0< or abort" expected: <nonnegative integer>"
;

: parse-positive ( "number" -- n )
  parse-number over 0<= or abort" expected: <positive integer>"
;

0 value |nodes|
defer nodes    \ V + -> (CRED CGREEN CBLUE or or)
defer edges    \ V cells + -> neighbors ...
0 value pq

: c postpone \
;

: p ( ``edge'' "nodes" "edges" -- )
  parse-name s" edge" compare abort" expected: p edge <nodes> <edges>"
  parse-nonnegative
    dup ->|nodes| 1+
    dup noname create latestxt is nodes [ CRED CGREEN CBLUE or or ] literal allot-init
        noname create latestxt is edges cells 0 allot-init
  parse-nonnegative drop
;

: e ( "u" "v" -- )
  parse-positive
  parse-positive
  2dup cells edges + >stack
  swap cells edges + >stack
;

: popcnt ( w - count )
  0 begin over while
    1+ swap dup 1- and swap
  repeat nip
;

\ Heuristic for the backtracking order. Returns true if node1 should be
\ assigned a color before node2.
: before ( node1 node2 -- b )
  \ TODO
  nodes tuck + c@ >r + c@ r> popcnt swap popcnt swap <
;

: pq-swap ( pq i j -- pq )
  cells third + swap cells third + ( pq j_addr i_addr )
  2dup swap-cells
  @ swap @ ( pq i_node j_node )
  third dup cell- @ cells + swap-array-elements
;

: left ( pq i -- left|0 )
  2* swap @ over >= and
;

: right ( pq i -- right|0 )
  2* 1+ swap @ over >= and
;

: parent ( i -- parent|0 )
  2/
;

\ Returns index of the node that should be colored first according
\ to a heuristic.
: favoured { pq fst snd } ( -- fst|snd )
  \ TODO
  pq fst cells + @ pq snd cells + @ before if fst else snd endif
;

: favoured-child ( pq i -- left|right|0 )
  2dup right if 2* dup 1+ favoured else left endif
;

: should-descend ( pq i -- child|0 )
  2dup favoured-child dup 0= if -rot 2drop exit endif
  dup >r favoured r> tuck = and
;

: should-ascend ( pq i -- parent|0 )
  dup parent dup 0= if -rot 2drop exit endif
  dup >r favoured r> tuck <> and
;

: heapify-down ( pq i -- ) recursive
  2dup should-descend ?dup 0= if 2drop exit endif
  dup >r pq-swap r> heapify-down
;

: heapify-up ( pq i -- ) recursive
  2dup should-ascend ?dup 0= if 2drop exit endif
  dup >r pq-swap r> heapify-up
;

\ Priority queue (max binary heap) memory layout:
\
\ +---+---+-------------------------+-------------------------+
\ |cap|len|           heap          |          lookup         |
\ +---+---+-------------------------+-------------------------+
\     ^    \                       / \                       /
\     pq     size == cells |nodes|     size == cells |nodes|
\
\ Note that pq doesn't point to the very beginning of the data structure. This
\ hacky solution simplifies address arithmetic for the heap and lookup regions
\ and allows to get the number of remaining element in the queue by simply
\ calling "pq @".
\
: pq-create ( size -- pq )
  align dup , here swap dup , dup cells allot ( pq size )
  1+ 1 u+do
    i cells over + i over ! ,
  loop
  dup @ parent 1 swap -[do
    dup i heapify-down
  -1 +loop
;

: pq-pop ( -- node )
  \ TODO refactor
  pq pq @ 2dup 1- swap ! ( pq size )
  2dup 1 pq-swap drop \ TODO ( pq size )
  swap dup 1 heapify-down ( size pq )
  swap cells over + @ ( pq node )
  over cell- @ + cells + ( node_lookup_addr )
  dup @ @ 0 rot !
;

: pq-push ( node -- )
  \ TODO refactor
  pq @ 1+ dup pq ! ( node new_size )
  tuck cells pq + 2dup ! ( new_size node node_addr )
  swap pq cell- @ + cells pq + ! ( new_size )
  pq swap heapify-up
;

: pq-adjust ( node -- )
  \ TODO some heuristics may require heapify down (or when restoring bitmasks)
  \ TODO refactor
  pq cell- @ + cells pq + @ ?dup 0<> if pq - cell/ pq swap heapify-up endif
;

: pq-empty? ( -- b )
  pq @ 0=
;

: foreach-neighbor ( node -- )
  ]] cells edges + $@ bounds +do [[
; immediate

: end-foreach ( -- )
  ]] cell +loop [[
; immediate

: iter ( -- neighbor )
  ]] i @ [[
; immediate

: propagate-to-neighbor ( color neighbor -- )
  tuck nodes + tuck c@ swap invert and swap c! pq-adjust
;

: set-color ( color node -- )
  foreach-neighbor
    dup iter propagate-to-neighbor
  end-foreach
  drop
;

defer backtrack

: backtrack-color ( node color -- b )
  swap 2dup nodes + c@ and 0= if 2drop false exit endif ( color node )

  2>r r@ foreach-neighbor
    iter nodes + c@ iter ( ... bitset neighbor )
  end-foreach

  2r@ set-color

  backtrack if
    r@ foreach-neighbor
      2drop
    end-foreach
    2r> ( colors node ) nodes + c! true
  else
    r@ foreach-neighbor
      tuck nodes + c! pq-adjust
    end-foreach
    2rdrop false
  endif
;

: _backtrack ( -- b )
  pq-empty? if true exit else pq-pop endif

              dup CRED backtrack-color
  ?dup 0= if  dup CGREEN backtrack-color endif
  ?dup 0= if  dup CBLUE backtrack-color endif
  ( node b )

  swap pq-push
;
' _backtrack is backtrack

: 3colorable? ( -- b )
  |nodes| pq-create ->pq
  nodes |nodes| %111 fill
  pq-empty? ?dup 0= if
    \ Do not backtrack the first node.
    pq-pop dup CRED backtrack-color swap pq-push
  endif
;

: output-color ( color -- )
  case
    CRED of s" tomato" endof
    CGREEN of s" mediumseagreen" endof
    CBLUE of s" skyblue" endof
    s" lightgray" rot
  endcase type
;

: output-graph ( -- )
  ." graph G {" cr
  |nodes| 1+ 1 +do
    ."   " i . ." [style=filled, fillcolor=" nodes i + c@ output-color ." ];" cr
  loop
  |nodes| 1+ 1 +do
      i foreach-neighbor
        j iter <= if
          ."   " j . ." -- " i @ 0 .r ." ;" cr
        endif
      end-foreach
  loop
  ." }" cr
;

: check ( -- )
  3colorable? if ." yes" else ." no" endif cr
;

: visualize ( -- )
  3colorable? drop
  s" dot -Tpng | feh -" w/o open-pipe throw
    ['] output-graph over outfile-execute
  close-file throw
;
