;; SECTION 1. VARIABLE DECLARATION
;*********************************
; Create patches/cells that represent geographic objects and are defined by the
; attributes version and p_error to track its interactions and quality.
; (We originally had cells split between different types of objects, nodes
; and ways based on the notion that nodes are easier geographical features
; to contribute so are prioritized and less likely to have errors. We removed
; this function in the final model and only used ways as generic geographic objects.)
breed [nodes node]
breed [ways way]

; Create moving turtles casuals and seniors as mappers who
; choose to edit geographical objects within a region. They
; are defined by attributes experience-type and frequency to determine
; the quality of their edits and how frequently they edit in
; a time stamp.
; (We originally attempted to incorporate multiple types of agents with
; different levels of experience and behavior. For the paper, we only
; used casual mapping agents, but the functionality for multiple types is
; still built into the model.)

breed [casuals casual]
breed [seniors senior]

patches-own [version p_error attract]

casuals-own [experience-type frequency]
seniors-own [experience-type frequency]

globals
[
  num_patches ; Number of patches in the model.
  mappers     ; Agentset of casuals and seniors.
  types       ; Agentset of nodes and ways.
  rand_temp   ; Hold for random calculations.
  nodes_count ; Number of nodes with versions > 0
  ways_count  ; ^
  time        ; Keep track of time lapsed.
  xcor_temp   ; Hold for agent coordinates for an extended Moore neighborhood.
  ycor_temp   ; ^
  nodes_acc   ; Average p_error of nodes.
  ways_acc    ; Average p_error of ways.
]
;; END OF SECTION 1. VARIABLE DECLARATION
;****************************************

;; SECTION 2. INITIALIZATION
;***************************
to setup
  clear-all

  ; Setup casual and senior agents.
  set-default-shape turtles "person"
  create-casuals casual-agents [
    set color cyan
    set experience-type 0
    set frequency casual-frequency
  ]
  create-seniors senior-agents [
    set color lime
    set experience-type 1
    set frequency senior-frequency
  ]
  ask turtles [
    set size 1.5
    setxy random-pxcor random-pycor
  ]
  set mappers (turtle-set casuals seniors)

  ; Setup patches as geographical objects and populate nodes and ways
  ; onto each patch. Default error set to 40 m.
  set-default-shape ways "triangle"
  ask patches [
    set version 0
    set p_error 40
    sprout-ways 1 [set color black set size 0.5]
    update-patch
  ]

  ; For adjusting the density of objects mapped.
  set num_patches count patches
  ask n-of ((1 - ratio-objects) * num_patches) ways [set breed nodes]
  set types (turtle-set nodes ways)

  ask nodes [hide-turtle]

  ;; INITIATE GLOBAL VARIABLES
  set time 0
  update-variables

  reset-ticks
end
;; END OF SECTION 2. INITIALIZATION
;**********************************

;; SECTION 3. SIMULATION
;***********************
to go
  ; Agents move to a new cell, then edit the cell.
  ask mappers [
    ;let freq_rand random frequency
    repeat frequency [move edit]]

  ; Create the version label on each cell.
  ask patches [
    if version > 0 [
      set plabel version
      set plabel-color green]]

  update-variables

  ask patches [update-patch]

  update-time

  ; Print final output values and stop the simulation at
  ; user-specified time period.
  if (time > runtime)[
    print ("Total No. of Objects:")
    print ways_count
    if (ways_count = 0)[set ways_count 1]
    print ("Avg p_error (m):")
    print (sum [p_error] of ways with [version > 0] / ways_count)
    print ("Avg Version:")
    print (sum [version] of ways / ways_count)
    stop]
  tick

  do-plots
end

;; PROCEDURES RELATED TO TURTLES (AGENTS)
;****************************************
to move
  ; Agents choose to move to a new cell in their modified Moore neighborhood
  ; based on a weighted randomization of each cell's attractiveness in the neighborhood.
  ; Attractiveness is calculated from a cell's error, where cells with larger error
  ; are weighted heavier in the randomization.

  ; Extend Moore neighborhood to user-defined number of layers. We used 2 layers, or
  ; a Moore neighborhood of 24 cells rather than letting agents have free reign of
  ; the environment to reduce the computational need.
  set xcor_temp xcor
  set ycor_temp ycor
  let neighbors24 patches with [
    pxcor <= xcor_temp + moore-size and pycor <= ycor_temp + moore-size and
    pxcor >= xcor_temp - moore-size and pycor >= ycor_temp - moore-size]
  let cand_ways ways-on neighbors24
  let target-patch one-of cand_ways

  ; Possible cells to move to set to the user-defined Moore neighborhood.
  let candidates neighbors24


  ; Set preference for editing nodes based on experience.
  ;let node_pref (50 + (1 - experience-type) * 50) / 100
  let node_pref 0  ; Ignore nodes, or in the current version, blank cells.
  ;let cand_nodes nodes-on neighbors24
  ;ask cand_nodes [set attract 0]

  ; Update attractiveness of each object based on its current
  ; p_error or whether it has been mapped yet. Set weight of
  ; unmapped cells with creation-priority.
  ask cand_ways [
    ifelse (version = 0)[
      set attract creation-priority][
      set attract 0.01 ^ (1 - p_error / 40)]]

  ; Weight each object within neighbors24 relative to other objects
  ; within the neighborhood. Sum of all attract within the
  ; neighborhood should equal 100.
  let attract_total sum [attract] of cand_ways
  ifelse (attract_total = 0)[][
    ask cand_ways [set attract (attract / attract_total) * 100]]

  ; Create list of attractiveness sorted by largest to smallest value.
  let list_temp sort-by [[a b] -> [attract] of a < [attract] of b] cand_ways

  ifelse (prioritybased-selection?) [
    set rand_temp random 100
    if (rand_temp = 0)[set rand_temp random 100]

    ; Select an object randomly based on its attractiveness weight.
    let i 0
    let j 0
    while [i < rand_temp and j < length list_temp][
      set i (i + ([attract] of item j list_temp))
      set j (j + 1)]

    ifelse (j > 0)[set target-patch item (j - 1) list_temp][
      set target-patch item 0 list_temp]

    ifelse (experience-type = 1) and ([attract] of item (j - 1) list_temp = 0)[][
      face target-patch
      move-to target-patch]

    ;if (experience-type = 1) and (attract_total < 0.01)[
    ;  set target-patch one-of cand_ways
    ;  face target-patch
    ;  move-to target-patch]
  ][
    face target-patch
    move-to target-patch]
end

; Once an agent moves to a new cell, they can edit the error
; of the cell. The quality of their edit is based on their
; agent-type's proficiency distribution. The proficiency distribution
; for each agent type is a gamma distribution characterized by a mean
; and variance parameter set by the user. In the current model,
; agents only update the error of a cell if it is an improvement.
to edit
  ; Define the mean and variance parameters.
  let alpha mean-p_error * mean-p_error / var-p_error
  let lambda mean-p_error / var-p_error

  let alpha2 mean-p_error2 * mean-p_error2 / var-p_error2
  let lambda2 mean-p_error2 / var-p_error2

  ; If agent is casual. Set up the gamma distribution using
  ; the parameters.
  if (experience-type = 0)[
    set rand_temp (random-gamma alpha lambda)
    ; Cap, assuming no roads should be off by more than 45m.
    if rand_temp > 45 [set rand_temp (random-gamma alpha lambda)]]
    ;set rand_temp (random 45)]  ; Test with a uniform distribution.

  ; If agent is senior.
  if (experience-type = 1)[
    set rand_temp (random-gamma alpha2 lambda2)
    if rand_temp > 45 [set rand_temp (random-gamma alpha2 lambda2)]]

  ; Agent decides not to make an edit if the p_error doesn't improve by more than 2%.
  ;if (100 - p_error) * rand_temp / 100 > 1.0 [
  ;  set p_error (p_error + (100 - p_error) * rand_temp / 100)
  ;  set version (version + 1)]

  ; Update the error of the cell if it is an improvement.
  if rand_temp < p_error [
      set p_error rand_temp
      set version (version + 1)]
end
;; END OF PROCEDURES RELATED TO TURTLES (AGENTS)
;***********************************************

;; PROCEDURES RELATED TO PATCHES (SPATIAL ENVIRONMENT)
;*****************************************************
to update-patch
  ; Set patch to be grey if the object hasn't been created yet.
  ; Once created, scale the patch color with the p_error of
  ; the object - red to white gradient.
  ifelse (version = 0)
  [set pcolor grey]
  [set pcolor scale-color red p_error 50 0]
end

;; END OF PROCEDURES RELATED TO PATCHES (SPATIAL ENVIRONMENT)
;************************************************************

;; GLOBAL VARIABLE UPDATE
;************************
to update-variables
  set ways_count count ways with [version > 0]  ; Track the number of cells mapped.

  ; Track the average error of all mapped cells in the environment.
  ifelse (ways_count > 0)[
    set ways_acc (sum [p_error] of ways / ways_count)][
    set ways_acc 0]
end

to update-time
  set time (time + 1)
end

;; UPDATE PLOTS
;**************
to do-plots
  set-current-plot "Number of Objects"
  set-current-plot-pen "Ways"
  plot ways_count

  let ver_list [0 0 0 0 0 0]
  let i 0
  while [i < 6][
    set ver_list replace-item i ver_list (count ways with [version = i] / count ways * 100)
    if (i = 5)[set ver_list replace-item i ver_list (count ways with [version > i] / count ways * 100)]
    set i (i + 1)
  ]

  set-current-plot "Object Versions"
  set-current-plot-pen "Not Mapped"
  plot item 0 ver_list
  set-current-plot-pen "V1"
  plot item 1 ver_list
  set-current-plot-pen "V2"
  plot item 2 ver_list
  set-current-plot-pen "V3"
  plot item 3 ver_list
  set-current-plot-pen "V4"
  plot item 4 ver_list
  set-current-plot-pen "V5+"
  plot item 5 ver_list

  let acc_list [0 0 0 0 0 0]
  set i 0
  while [i < 6][
    set acc_list replace-item i acc_list (
      count ways with [p_error > (i * 5) and p_error <= (i * 5 + 5)] / count ways * 100)
    if (i = 5)[
      set acc_list replace-item i acc_list (
        count ways with [version = 0] / count ways * 100)]
    if (i = 4)[
      set acc_list replace-item i acc_list (
        count ways with [p_error > (i * 5) and version > 0] / count ways * 100)]
    set i (i + 1)
  ]

  set-current-plot "Object Error"
  set-current-plot-pen "Not Mapped"
  plot item 5 acc_list
  set-current-plot-pen "[20, inf)"
  plot item 4 acc_list
  set-current-plot-pen "[15, 20)"
  plot item 3 acc_list
  set-current-plot-pen "[10, 15)"
  plot item 2 acc_list
  set-current-plot-pen "[5, 10)"
  plot item 1 acc_list
  set-current-plot-pen "[0, 5)"
  plot item 0 acc_list

  set-current-plot "Error Freq."
  set-plot-pen-mode 1
  set-current-plot-pen "Ways"
  histogram [p_error] of ways with [version > 0]

end

;; END OF SECTION 3. SIMULATION
;******************************
@#$#@#$#@
GRAPHICS-WINDOW
260
15
688
444
-1
-1
20.0
1
10
1
1
1
0
0
0
1
0
20
0
20
0
0
1
ticks
30.0

BUTTON
90
35
153
68
NIL
go
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
10
35
83
68
NIL
setup
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

INPUTBOX
10
80
130
140
senior-agents
1.0
1
0
Number

SWITCH
10
415
250
448
prioritybased-selection?
prioritybased-selection?
0
1
-1000

SLIDER
10
380
250
413
ratio-objects
ratio-objects
0
1
1.0
0.01
1
NIL
HORIZONTAL

INPUTBOX
10
140
130
200
senior-frequency
5.0
1
0
Number

INPUTBOX
130
140
250
200
casual-frequency
5.0
1
0
Number

INPUTBOX
165
15
250
75
runtime
15.0
1
0
Number

PLOT
695
15
915
205
Number of Objects
Time
No. of Objects
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"Ways" 1.0 0 -817084 true "" ""

PLOT
695
395
1010
580
Object Versions
Time
% of Objects
0.0
10.0
0.0
101.0
true
true
"" ""
PENS
"Not Mapped" 1.0 0 -4539718 true "" ""
"V1" 1.0 0 -955883 true "" ""
"V2" 1.0 0 -13840069 true "" ""
"V3" 1.0 0 -13791810 true "" ""
"V4" 1.0 0 -8630108 true "" ""
"V5+" 1.0 0 -5825686 true "" ""

PLOT
695
205
1010
395
Object Error
Time
% of Objects
0.0
10.0
0.0
100.0
true
true
"" ""
PENS
"Not Mapped" 1.0 0 -4539718 true "" ""
"[20, inf)" 1.0 0 -16777216 true "" ""
"[15, 20)" 1.0 0 -5298144 true "" ""
"[10, 15)" 1.0 0 -6917194 true "" ""
"[5, 10)" 1.0 0 -13791810 true "" ""
"[0, 5)" 1.0 0 -13840069 true "" ""

PLOT
915
15
1185
205
Error Freq.
Error (m)
No. of Objects
0.0
45.0
0.0
150.0
false
false
"" ""
PENS
"Ways" 1.0 0 -14454117 true "" ""

INPUTBOX
130
80
250
140
casual-agents
0.0
1
0
Number

SLIDER
10
225
250
258
mean-p_error
mean-p_error
0
50
16.0
1
1
m
HORIZONTAL

SLIDER
10
255
250
288
var-p_error
var-p_error
1
50
50.0
1
1
m
HORIZONTAL

SLIDER
10
310
250
343
mean-p_error2
mean-p_error2
0
50
10.0
1
1
m
HORIZONTAL

SLIDER
10
340
250
373
var-p_error2
var-p_error2
1
50
30.0
1
1
m
HORIZONTAL

TEXTBOX
10
295
160
313
Senior Proficiency:
12
0.0
1

TEXTBOX
10
205
160
223
Casual Proficiency:
12
0.0
1

SLIDER
10
450
250
483
creation-priority
creation-priority
0
1.0
0.01
0.01
1
NIL
HORIZONTAL

INPUTBOX
10
485
110
545
moore-size
2.0
1
0
Number

TEXTBOX
120
490
270
570
moore-size: neighbors\n1: 8\n2: 24\n3: 48\n4: 80
12
0.0
1

@#$#@#$#@
## WHAT IS IT?

(a general understanding of what the model is trying to show or explain)

## HOW IT WORKS

(what rules the agents use to create the overall behavior of the model)

## HOW TO USE IT

(how to use the model, including a description of each of the items in the Interface tab)

## THINGS TO NOTICE

(suggested things for the user to notice while running the model)

## THINGS TO TRY

(suggested things for the user to try to do (move sliders, switches, etc.) with the model)

## EXTENDING THE MODEL

(suggested things to add or change in the Code tab to make the model more complicated, detailed, accurate, etc.)

## NETLOGO FEATURES

(interesting or unusual features of NetLogo that the model uses, particularly in the Code tab; or where workarounds were needed for missing features)

## RELATED MODELS

(models in the NetLogo Models Library and elsewhere which are of related interest)

## CREDITS AND REFERENCES

(a reference to the model's URL on the web if it has one, as well as any other necessary credits, citations, and links)
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

sheep
false
15
Circle -1 true true 203 65 88
Circle -1 true true 70 65 162
Circle -1 true true 150 105 120
Polygon -7500403 true false 218 120 240 165 255 165 278 120
Circle -7500403 true false 214 72 67
Rectangle -1 true true 164 223 179 298
Polygon -1 true true 45 285 30 285 30 240 15 195 45 210
Circle -1 true true 3 83 150
Rectangle -1 true true 65 221 80 296
Polygon -1 true true 195 285 210 285 210 240 240 210 195 210
Polygon -7500403 true false 276 85 285 105 302 99 294 83
Polygon -7500403 true false 219 85 210 105 193 99 201 83

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

wolf
false
0
Polygon -16777216 true false 253 133 245 131 245 133
Polygon -7500403 true true 2 194 13 197 30 191 38 193 38 205 20 226 20 257 27 265 38 266 40 260 31 253 31 230 60 206 68 198 75 209 66 228 65 243 82 261 84 268 100 267 103 261 77 239 79 231 100 207 98 196 119 201 143 202 160 195 166 210 172 213 173 238 167 251 160 248 154 265 169 264 178 247 186 240 198 260 200 271 217 271 219 262 207 258 195 230 192 198 210 184 227 164 242 144 259 145 284 151 277 141 293 140 299 134 297 127 273 119 270 105
Polygon -7500403 true true -1 195 14 180 36 166 40 153 53 140 82 131 134 133 159 126 188 115 227 108 236 102 238 98 268 86 269 92 281 87 269 103 269 113

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.2.2
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
<experiments>
  <experiment name="world size" repetitions="2" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <metric>sum [p_error] of ways with [version &gt; 0] / ways_count</metric>
    <enumeratedValueSet variable="var-p_error">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="casual-frequency">
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="ratio-objects">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mean-p_error">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="casual-agents">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mean-p_error2">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="senior-agents">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="senior-frequency">
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="intelligent-selection?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="runtime">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="var-p_error2">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max-pxcor">
      <value value="10"/>
      <value value="20"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max-pycor">
      <value value="10"/>
      <value value="20"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="num-agents" repetitions="10" runMetricsEveryStep="true">
    <setup>setup</setup>
    <go>go</go>
    <metric>sum [p_error] of ways with [version &gt; 0] / ways_count</metric>
    <metric>ways_count</metric>
    <metric>sum [version] of ways with [version &gt; 0] / ways_count</metric>
    <enumeratedValueSet variable="var-p_error">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="casual-frequency">
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="ratio-objects">
      <value value="1"/>
    </enumeratedValueSet>
    <steppedValueSet variable="casual-agents" first="0" step="1" last="32"/>
    <enumeratedValueSet variable="mean-p_error">
      <value value="16"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mean-p_error2">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="senior-agents">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="senior-frequency">
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="creation-priority">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="intelligent-selection?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="runtime">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="var-p_error2">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max-pxcor">
      <value value="20"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max-pycor">
      <value value="20"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="moore-size">
      <value value="2"/>
    </enumeratedValueSet>
  </experiment>
</experiments>
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180
@#$#@#$#@
1
@#$#@#$#@
