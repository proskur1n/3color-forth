#! /bin/env -S gforth -e bye

%001 constant CRED
%010 constant CGREEN
%100 constant CBLUE

: allot-init ( u c -- )
  here -rot over allot fill
;

: parse-positive
  parse-name s>number d>s \ TODO check > 0 and not empty
;

: parse-vertex
  parse-positive
;

0 value |nodes|
defer nodes    \ V + -> (CRED CGREEN CBLUE or or)
defer edges    \ V cells + -> neighbors ...
0 value pq

: c postpone \
;

: p ( ``edge'' "nodes" "edges" -- )
  parse-name s" edge" compare abort" expected: p edge <nodes> <edges>"
  parse-positive
    dup ->|nodes| 1+
    dup noname create latestxt is nodes [ CRED CGREEN CBLUE or or ] literal allot-init
        noname create latestxt is edges cells 0 allot-init
  parse-positive drop
;

: e ( "u" "v" -- )
  parse-vertex
  parse-vertex
  2dup cells edges + >stack
  swap cells edges + >stack
;

: pq-create ( size -- pq )
  here over dup , cells allot swap ( pq size )
  1+ 1 u+do i over i cells + ! loop
;

: pq-pop ( -- node ) \ TODO heapify
  pq dup @ 2dup 1- swap ! cells + @
;

: pq-push ( node -- ) \ TODO heapify
  pq dup @ 1+ 2dup swap ! cells + !
;

: pq-adjust ( node -- )
  drop \ TODO
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
