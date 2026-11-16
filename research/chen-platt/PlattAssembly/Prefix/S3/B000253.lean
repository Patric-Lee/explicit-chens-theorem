import PlattAssemblyKernel
import PlattCertificates.Count131072.C028096
import PlattCertificates.Count131072.C028097
import PlattCertificates.Count131072.C028098
import PlattCertificates.Count131072.C028099
import PlattCertificates.Count131072.C028100
import PlattCertificates.Count131072.C028101
import PlattCertificates.Count131072.C028102
import PlattCertificates.Count131072.C028103
import PlattCertificates.Count131072.C028104
import PlattCertificates.Count131072.C028105
import PlattCertificates.Count131072.C028106
import PlattCertificates.Count131072.C028107
import PlattCertificates.Count131072.C028108
import PlattCertificates.Count131072.C028109
import PlattCertificates.Count131072.C028110
import PlattCertificates.Count131072.C028111
import PlattCertificates.Count131072.C028112
import PlattCertificates.Count131072.C028113
import PlattCertificates.Count131072.C028114
import PlattCertificates.Count131072.C028115
import PlattCertificates.Count131072.C028116
import PlattCertificates.Count131072.C028117
import PlattCertificates.Count131072.C028118
import PlattCertificates.Count131072.C028119
import PlattCertificates.Count131072.C028120
import PlattCertificates.Count131072.C028121
import PlattCertificates.Count131072.C028122
import PlattCertificates.Count131072.C028123
import PlattCertificates.Count131072.C028124
import PlattCertificates.Count131072.C028125
import PlattCertificates.Count131072.C028126
import PlattCertificates.Count131072.C028127
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000253
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28096 : List PrefixCut := [⟨42,145221103,145221186⟩,
⟨128,453753214,453753469⟩]
theorem checked28096 : checkPrefixCuts (2^48) 3686531073 9 Manual.Count131072.C028096.packed 128 cuts28096 = true := by
 decide +kernel
def pointBounds28096 : List (Nat × Nat × Nat) := [(3686574080,104392379518610,104392762371674)]
theorem point_links_checked28096 : (cuts28096.take 1).map (fun c => (3686531073-1+2*2^9*c.k,104392234297507+c.lower,104392617150488+c.upper)) = pointBounds28096 := by
 decide +kernel
def cuts28097 : List PrefixCut := [⟨27,97345267,97345321⟩,
⟨128,455340472,455340725⟩]
theorem checked28097 : checkPrefixCuts (2^48) 3686662145 9 Manual.Count131072.C028097.packed 128 cuts28097 = true := by
 decide +kernel
def pointBounds28097 : List (Nat × Nat × Nat) := [(3686689792,104392785395988,104393168249278)]
theorem point_links_checked28097 : (cuts28097.take 1).map (fun c => (3686662145-1+2*2^9*c.k,104392688050721+c.lower,104393070903957+c.upper)) = pointBounds28097 := by
 decide +kernel
def cuts28098 : List PrefixCut := [⟨12,42067023,42067046⟩,
⟨125,444865122,444865369⟩,
⟨128,455705988,455706241⟩]
theorem checked28098 : checkPrefixCuts (2^48) 3686793217 9 Manual.Count131072.C028098.packed 128 cuts28098 = true := by
 decide +kernel
def pointBounds28098 : List (Nat × Nat × Nat) := [(3686805504,104393185458216,104393568311728),(3686921216,104393588256315,104393971110051)]
theorem point_links_checked28098 : (cuts28098.take 2).map (fun c => (3686793217-1+2*2^9*c.k,104393143391193+c.lower,104393526244682+c.upper)) = pointBounds28098 := by
 decide +kernel
def cuts28099 : List PrefixCut := [⟨110,388280137,388280350⟩,
⟨128,454086572,454086821⟩]
theorem checked28099 : checkPrefixCuts (2^48) 3686924289 9 Manual.Count131072.C028099.packed 128 cuts28099 = true := by
 decide +kernel
def pointBounds28099 : List (Nat × Nat × Nat) := [(3687036928,104393987377318,104394370231273)]
theorem point_links_checked28099 : (cuts28099.take 1).map (fun c => (3686924289-1+2*2^9*c.k,104393599097181+c.lower,104393981950923+c.upper)) = pointBounds28099 := by
 decide +kernel
def cuts28100 : List PrefixCut := [⟨95,336203028,336203214⟩,
⟨128,453841462,453841716⟩]
theorem checked28100 : checkPrefixCuts (2^48) 3687055361 9 Manual.Count131072.C028100.packed 128 cuts28100 = true := by
 decide +kernel
def pointBounds28100 : List (Nat × Nat × Nat) := [(3687152640,104394389386781,104394772240958)]
theorem point_links_checked28100 : (cuts28100.take 1).map (fun c => (3687055361-1+2*2^9*c.k,104394053183753+c.lower,104394436037744+c.upper)) = pointBounds28100 := by
 decide +kernel
def cuts28101 : List PrefixCut := [⟨80,283976709,283976868⟩,
⟨128,451382562,451382815⟩]
theorem checked28101 : checkPrefixCuts (2^48) 3687186433 9 Manual.Count131072.C028101.packed 128 cuts28101 = true := by
 decide +kernel
def pointBounds28101 : List (Nat × Nat × Nat) := [(3687268352,104394791001924,104395173856328)]
theorem point_links_checked28101 : (cuts28101.take 1).map (fun c => (3687186433-1+2*2^9*c.k,104394507025215+c.lower,104394889879460+c.upper)) = pointBounds28101 := by
 decide +kernel
def cuts28102 : List PrefixCut := [⟨65,238089680,238089811⟩,
⟨128,464954069,464954325⟩]
theorem checked28102 : checkPrefixCuts (2^48) 3687317505 9 Manual.Count131072.C028102.packed 128 cuts28102 = true := by
 decide +kernel
def pointBounds28102 : List (Nat × Nat × Nat) := [(3687384064,104395196497457,104395579352086)]
theorem point_links_checked28102 : (cuts28102.take 1).map (fun c => (3687317505-1+2*2^9*c.k,104394958407777+c.lower,104395341262275+c.upper)) = pointBounds28102 := by
 decide +kernel
def cuts28103 : List PrefixCut := [⟨50,177626225,177626324⟩,
⟨128,453869399,453869655⟩]
theorem checked28103 : checkPrefixCuts (2^48) 3687448577 9 Manual.Count131072.C028103.packed 128 cuts28103 = true := by
 decide +kernel
def pointBounds28103 : List (Nat × Nat × Nat) := [(3687499776,104395600988071,104395983842924)]
theorem point_links_checked28103 : (cuts28103.take 1).map (fun c => (3687448577-1+2*2^9*c.k,104395423361846+c.lower,104395806216600+c.upper)) = pointBounds28103 := by
 decide +kernel
def cuts28104 : List PrefixCut := [⟨35,124341818,124341888⟩,
⟨128,457364345,457364602⟩]
theorem checked28104 : checkPrefixCuts (2^48) 3687579649 9 Manual.Count131072.C028104.packed 128 cuts28104 = true := by
 decide +kernel
def pointBounds28104 : List (Nat × Nat × Nat) := [(3687615488,104396001573063,104396384428143)]
theorem point_links_checked28104 : (cuts28104.take 1).map (fun c => (3687579649-1+2*2^9*c.k,104395877231245+c.lower,104396260086255+c.upper)) = pointBounds28104 := by
 decide +kernel
def cuts28105 : List PrefixCut := [⟨20,68923820,68923859⟩,
⟨128,450555069,450555321⟩]
theorem checked28105 : checkPrefixCuts (2^48) 3687710721 9 Manual.Count131072.C028105.packed 128 cuts28105 = true := by
 decide +kernel
def pointBounds28105 : List (Nat × Nat × Nat) := [(3687731200,104396403519410,104396786374716)]
theorem point_links_checked28105 : (cuts28105.take 1).map (fun c => (3687710721-1+2*2^9*c.k,104396334595590+c.lower,104396717450857+c.upper)) = pointBounds28105 := by
 decide +kernel
def cuts28106 : List PrefixCut := [⟨5,17707411,17707422⟩,
⟨118,419857489,419857726⟩,
⟨128,455652740,455652996⟩]
theorem checked28106 : checkPrefixCuts (2^48) 3687841793 9 Manual.Count131072.C028106.packed 128 cuts28106 = true := by
 decide +kernel
def pointBounds28106 : List (Nat × Nat × Nat) := [(3687846912,104396802858070,104397185713600),(3687962624,104397205008148,104397587863904)]
theorem point_links_checked28106 : (cuts28106.take 2).map (fun c => (3687841793-1+2*2^9*c.k,104396785150659+c.lower,104397168006178+c.upper)) = pointBounds28106 := by
 decide +kernel
def cuts28107 : List PrefixCut := [⟨103,366952768,366952975⟩,
⟨128,454110144,454110399⟩]
theorem checked28107 : checkPrefixCuts (2^48) 3687972865 9 Manual.Count131072.C028107.packed 128 cuts28107 = true := by
 decide +kernel
def pointBounds28107 : List (Nat × Nat × Nat) := [(3688078336,104397607756167,104397990612149)]
theorem point_links_checked28107 : (cuts28107.take 1).map (fun c => (3687972865-1+2*2^9*c.k,104397240803399+c.lower,104397623659174+c.upper)) = pointBounds28107 := by
 decide +kernel
def cuts28108 : List PrefixCut := [⟨88,304206494,304206666⟩,
⟨128,449438499,449438752⟩]
theorem checked28108 : checkPrefixCuts (2^48) 3688103937 9 Manual.Count131072.C028108.packed 128 cuts28108 = true := by
 decide +kernel
def pointBounds28108 : List (Nat × Nat × Nat) := [(3688194048,104397999120037,104398381976239)]
theorem point_links_checked28108 : (cuts28108.take 1).map (fun c => (3688103937-1+2*2^9*c.k,104397694913543+c.lower,104398077769573+c.upper)) = pointBounds28108 := by
 decide +kernel
def cuts28109 : List PrefixCut := [⟨73,259551376,259551520⟩,
⟨128,452780548,452780801⟩]
theorem checked28109 : checkPrefixCuts (2^48) 3688235009 9 Manual.Count131072.C028109.packed 128 cuts28109 = true := by
 decide +kernel
def pointBounds28109 : List (Nat × Nat × Nat) := [(3688309760,104398403903418,104398786759845)]
theorem point_links_checked28109 : (cuts28109.take 1).map (fun c => (3688235009-1+2*2^9*c.k,104398144352042+c.lower,104398527208325+c.upper)) = pointBounds28109 := by
 decide +kernel
def cuts28110 : List PrefixCut := [⟨58,204367937,204368050⟩,
⟨128,448414640,448414892⟩]
theorem checked28110 : checkPrefixCuts (2^48) 3688366081 9 Manual.Count131072.C028110.packed 128 cuts28110 = true := by
 decide +kernel
def pointBounds28110 : List (Nat × Nat × Nat) := [(3688425472,104398801500527,104399184357176)]
theorem point_links_checked28110 : (cuts28110.take 1).map (fun c => (3688366081-1+2*2^9*c.k,104398597132590+c.lower,104398979989126+c.upper)) = pointBounds28110 := by
 decide +kernel
def cuts28111 : List PrefixCut := [⟨43,152087999,152088086⟩,
⟨128,452824636,452824894⟩]
theorem checked28111 : checkPrefixCuts (2^48) 3688497153 9 Manual.Count131072.C028111.packed 128 cuts28111 = true := by
 decide +kernel
def pointBounds28111 : List (Nat × Nat × Nat) := [(3688541184,104399197635229,104399580492104)]
theorem point_links_checked28111 : (cuts28111.take 1).map (fun c => (3688497153-1+2*2^9*c.k,104399045547230+c.lower,104399428404018+c.upper)) = pointBounds28111 := by
 decide +kernel
def cuts28112 : List PrefixCut := [⟨28,99048470,99048525⟩,
⟨128,452045454,452045704⟩]
theorem checked28112 : checkPrefixCuts (2^48) 3688628225 9 Manual.Count131072.C028112.packed 128 cuts28112 = true := by
 decide +kernel
def pointBounds28112 : List (Nat × Nat × Nat) := [(3688656896,104399597420336,104399980277437)]
theorem point_links_checked28112 : (cuts28112.take 1).map (fun c => (3688628225-1+2*2^9*c.k,104399498371866+c.lower,104399881228912+c.upper)) = pointBounds28112 := by
 decide +kernel
def cuts28113 : List PrefixCut := [⟨13,45478363,45478389⟩,
⟨126,443407093,443407344⟩,
⟨128,450961133,450961388⟩]
theorem checked28113 : checkPrefixCuts (2^48) 3688759297 9 Manual.Count131072.C028113.packed 128 cuts28113 = true := by
 decide +kernel
def pointBounds28113 : List (Nat × Nat × Nat) := [(3688772608,104399995895683,104400378753005),(3688888320,104400393824413,104400776681960)]
theorem point_links_checked28113 : (cuts28113.take 2).map (fun c => (3688759297-1+2*2^9*c.k,104399950417320+c.lower,104400333274616+c.upper)) = pointBounds28113 := by
 decide +kernel
def cuts28114 : List PrefixCut := [⟨111,396084841,396085063⟩,
⟨128,457659646,457659904⟩]
theorem checked28114 : checkPrefixCuts (2^48) 3688890369 9 Manual.Count131072.C028114.packed 128 cuts28114 = true := by
 decide +kernel
def pointBounds28114 : List (Nat × Nat × Nat) := [(3689004032,104400797463294,104401180321067)]
theorem point_links_checked28114 : (cuts28114.take 1).map (fun c => (3688890369-1+2*2^9*c.k,104400401378453+c.lower,104400784236004+c.upper)) = pointBounds28114 := by
 decide +kernel
def cuts28115 : List PrefixCut := [⟨96,345866405,345866598⟩,
⟨128,455964887,455965142⟩]
theorem checked28115 : checkPrefixCuts (2^48) 3689021441 9 Manual.Count131072.C028115.packed 128 cuts28115 = true := by
 decide +kernel
def pointBounds28115 : List (Nat × Nat × Nat) := [(3689119744,104401204904504,104401587762506)]
theorem point_links_checked28115 : (cuts28115.take 1).map (fun c => (3689021441-1+2*2^9*c.k,104400859038099+c.lower,104401241895908+c.upper)) = pointBounds28115 := by
 decide +kernel
def cuts28116 : List PrefixCut := [⟨81,285046027,285046189⟩,
⟨128,455338177,455338436⟩]
theorem checked28116 : checkPrefixCuts (2^48) 3689152513 9 Manual.Count131072.C028116.packed 128 cuts28116 = true := by
 decide +kernel
def pointBounds28116 : List (Nat × Nat × Nat) := [(3689235456,104401600049013,104401982907239)]
theorem point_links_checked28116 : (cuts28116.take 1).map (fun c => (3689152513-1+2*2^9*c.k,104401315002986+c.lower,104401697861050+c.upper)) = pointBounds28116 := by
 decide +kernel
def cuts28117 : List PrefixCut := [⟨66,233919154,233919285⟩,
⟨128,455474663,455474917⟩]
theorem checked28117 : checkPrefixCuts (2^48) 3689283585 9 Manual.Count131072.C028117.packed 128 cuts28117 = true := by
 decide +kernel
def pointBounds28117 : List (Nat × Nat × Nat) := [(3689351168,104402004260317,104402387118771)]
theorem point_links_checked28117 : (cuts28117.take 1).map (fun c => (3689283585-1+2*2^9*c.k,104401770341163+c.lower,104402153199486+c.upper)) = pointBounds28117 := by
 decide +kernel
def cuts28118 : List PrefixCut := [⟨51,184397819,184397925⟩,
⟨128,455916305,455916565⟩]
theorem checked28118 : checkPrefixCuts (2^48) 3689414657 9 Manual.Count131072.C028118.packed 128 cuts28118 = true := by
 decide +kernel
def pointBounds28118 : List (Nat × Nat × Nat) := [(3689466880,104402410213645,104402793072328)]
theorem point_links_checked28118 : (cuts28118.take 1).map (fun c => (3689414657-1+2*2^9*c.k,104402225815826+c.lower,104402608674403+c.upper)) = pointBounds28118 := by
 decide +kernel
def cuts28119 : List PrefixCut := [⟨36,129844686,129844758⟩,
⟨128,457349611,457349866⟩]
theorem checked28119 : checkPrefixCuts (2^48) 3689545729 9 Manual.Count131072.C028119.packed 128 cuts28119 = true := by
 decide +kernel
def pointBounds28119 : List (Nat × Nat × Nat) := [(3689582592,104402811576817,104403194435726)]
theorem point_links_checked28119 : (cuts28119.take 1).map (fun c => (3689545729-1+2*2^9*c.k,104402681732131+c.lower,104403064590968+c.upper)) = pointBounds28119 := by
 decide +kernel
def cuts28120 : List PrefixCut := [⟨21,73388013,73388053⟩,
⟨128,451840712,451840961⟩]
theorem checked28120 : checkPrefixCuts (2^48) 3689676801 9 Manual.Count131072.C028120.packed 128 cuts28120 = true := by
 decide +kernel
def pointBounds28120 : List (Nat × Nat × Nat) := [(3689698304,104403212469755,104403595328887)]
theorem point_links_checked28120 : (cuts28120.take 1).map (fun c => (3689676801-1+2*2^9*c.k,104403139081742+c.lower,104403521940834+c.upper)) = pointBounds28120 := by
 decide +kernel
def cuts28121 : List PrefixCut := [⟨6,21054484,21054497⟩,
⟨119,430313373,430313613⟩,
⟨128,460292127,460292383⟩]
theorem checked28121 : checkPrefixCuts (2^48) 3689807873 9 Manual.Count131072.C028121.packed 128 cuts28121 = true := by
 decide +kernel
def pointBounds28121 : List (Nat × Nat × Nat) := [(3689814016,104403611976938,104403994836292),(3689929728,104404021235827,104404404095408)]
theorem point_links_checked28121 : (cuts28121.take 2).map (fun c => (3689807873-1+2*2^9*c.k,104403590922454+c.lower,104403973781795+c.upper)) = pointBounds28121 := by
 decide +kernel
def cuts28122 : List PrefixCut := [⟨104,359739469,359739674⟩,
⟨128,445248525,445248779⟩]
theorem checked28122 : checkPrefixCuts (2^48) 3689938945 9 Manual.Count131072.C028122.packed 128 cuts28122 = true := by
 decide +kernel
def pointBounds28122 : List (Nat × Nat × Nat) := [(3690045440,104404410954050,104404793813852)]
theorem point_links_checked28122 : (cuts28122.take 1).map (fun c => (3689938945-1+2*2^9*c.k,104404051214581+c.lower,104404434074178+c.upper)) = pointBounds28122 := by
 decide +kernel
def cuts28123 : List PrefixCut := [⟨89,315867507,315867684⟩,
⟨128,457437100,457437350⟩]
theorem checked28123 : checkPrefixCuts (2^48) 3690070017 9 Manual.Count131072.C028123.packed 128 cuts28123 = true := by
 decide +kernel
def pointBounds28123 : List (Nat × Nat × Nat) := [(3690161152,104404812330613,104405195190641)]
theorem point_links_checked28123 : (cuts28123.take 1).map (fun c => (3690070017-1+2*2^9*c.k,104404496463106+c.lower,104404879322957+c.upper)) = pointBounds28123 := by
 decide +kernel
def cuts28124 : List PrefixCut := [⟨74,260938563,260938708⟩,
⟨128,451090075,451090324⟩]
theorem checked28124 : checkPrefixCuts (2^48) 3690201089 9 Manual.Count131072.C028124.packed 128 cuts28124 = true := by
 decide +kernel
def pointBounds28124 : List (Nat × Nat × Nat) := [(3690276864,104405214838769,104405597699015)]
theorem point_links_checked28124 : (cuts28124.take 1).map (fun c => (3690201089-1+2*2^9*c.k,104404953900206+c.lower,104405336760307+c.upper)) = pointBounds28124 := by
 decide +kernel
def cuts28125 : List PrefixCut := [⟨59,208072650,208072764⟩,
⟨128,452752014,452752263⟩]
theorem checked28125 : checkPrefixCuts (2^48) 3690332161 9 Manual.Count131072.C028125.packed 128 cuts28125 = true := by
 decide +kernel
def pointBounds28125 : List (Nat × Nat × Nat) := [(3690392576,104405613062931,104405995923395)]
theorem point_links_checked28125 : (cuts28125.take 1).map (fun c => (3690332161-1+2*2^9*c.k,104405404990281+c.lower,104405787850631+c.upper)) = pointBounds28125 := by
 decide +kernel
def cuts28126 : List PrefixCut := [⟨44,152540827,152540916⟩,
⟨128,455862907,455863167⟩]
theorem checked28126 : checkPrefixCuts (2^48) 3690463233 9 Manual.Count131072.C028126.packed 128 cuts28126 = true := by
 decide +kernel
def pointBounds28126 : List (Nat × Nat × Nat) := [(3690508288,104406010283122,104406393143810)]
theorem point_links_checked28126 : (cuts28126.take 1).map (fun c => (3690463233-1+2*2^9*c.k,104405857742295+c.lower,104406240602894+c.upper)) = pointBounds28126 := by
 decide +kernel
def cuts28127 : List PrefixCut := [⟨29,101817607,101817664⟩,
⟨128,453940046,453940297⟩]
theorem checked28127 : checkPrefixCuts (2^48) 3690594305 9 Manual.Count131072.C028127.packed 128 cuts28127 = true := by
 decide +kernel
def pointBounds28127 : List (Nat × Nat × Nat) := [(3690624000,104406415422809,104406798283725)]
theorem point_links_checked28127 : (cuts28127.take 1).map (fun c => (3690594305-1+2*2^9*c.k,104406313605202+c.lower,104406696466061+c.upper)) = pointBounds28127 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000253
