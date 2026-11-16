import PlattAssemblyKernel
import PlattCertificates.Count131072.C041120
import PlattCertificates.Count131072.C041121
import PlattCertificates.Count131072.C041122
import PlattCertificates.Count131072.C041123
import PlattCertificates.Count131072.C041124
import PlattCertificates.Count131072.C041125
import PlattCertificates.Count131072.C041126
import PlattCertificates.Count131072.C041127
import PlattCertificates.Count131072.C041128
import PlattCertificates.Count131072.C041129
import PlattCertificates.Count131072.C041130
import PlattCertificates.Count131072.C041131
import PlattCertificates.Count131072.C041132
import PlattCertificates.Count131072.C041133
import PlattCertificates.Count131072.C041134
import PlattCertificates.Count131072.C041135
import PlattCertificates.Count131072.C041136
import PlattCertificates.Count131072.C041137
import PlattCertificates.Count131072.C041138
import PlattCertificates.Count131072.C041139
import PlattCertificates.Count131072.C041140
import PlattCertificates.Count131072.C041141
import PlattCertificates.Count131072.C041142
import PlattCertificates.Count131072.C041143
import PlattCertificates.Count131072.C041144
import PlattCertificates.Count131072.C041145
import PlattCertificates.Count131072.C041146
import PlattCertificates.Count131072.C041147
import PlattCertificates.Count131072.C041148
import PlattCertificates.Count131072.C041149
import PlattCertificates.Count131072.C041150
import PlattCertificates.Count131072.C041151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts41120 : List PrefixCut := [⟨4,18421894,18421906⟩,
⟨64,302835772,302835951⟩]
theorem checked41120 : checkPrefixCuts (2^48) 5393612801 10 Manual.Count131072.C041120.packed 64 cuts41120 = true := by
 decide +kernel
def pointBounds41120 : List (Nat × Nat × Nat) := [(5393620992,109213061026176,109213446737095)]
theorem point_links_checked41120 : (cuts41120.take 1).map (fun c => (5393612801-1+2*2^10*c.k,109213042604282+c.lower,109213428315189+c.upper)) = pointBounds41120 := by
 decide +kernel
def cuts41121 : List PrefixCut := [⟨23,110319540,110319603⟩,
⟨64,306794473,306794655⟩]
theorem checked41121 : checkPrefixCuts (2^48) 5393743873 10 Manual.Count131072.C041121.packed 64 cuts41121 = true := by
 decide +kernel
def pointBounds41121 : List (Nat × Nat × Nat) := [(5393790976,109213455759594,109213841470743)]
theorem point_links_checked41121 : (cuts41121.take 1).map (fun c => (5393743873-1+2*2^10*c.k,109213345440054+c.lower,109213731151140+c.upper)) = pointBounds41121 := by
 decide +kernel
def cuts41122 : List PrefixCut := [⟨42,199602881,199603000⟩,
⟨64,305325890,305326069⟩]
theorem checked41122 : checkPrefixCuts (2^48) 5393874945 10 Manual.Count131072.C041122.packed 64 cuts41122 = true := by
 decide +kernel
def pointBounds41122 : List (Nat × Nat × Nat) := [(5393960960,109213851837408,109214237548795)]
theorem point_links_checked41122 : (cuts41122.take 1).map (fun c => (5393874945-1+2*2^10*c.k,109213652234527+c.lower,109214037945795+c.upper)) = pointBounds41122 := by
 decide +kernel
def cuts41123 : List PrefixCut := [⟨61,292273077,292273249⟩,
⟨64,305370674,305370855⟩]
theorem checked41123 : checkPrefixCuts (2^48) 5394006017 10 Manual.Count131072.C041123.packed 64 cuts41123 = true := by
 decide +kernel
def pointBounds41123 : List (Nat × Nat × Nat) := [(5394130944,109214249833494,109214635545113)]
theorem point_links_checked41123 : (cuts41123.take 1).map (fun c => (5394006017-1+2*2^10*c.k,109213957560417+c.lower,109214343271864+c.upper)) = pointBounds41123 := by
 decide +kernel
def cuts41124 : List PrefixCut := [⟨64,305780656,305780838⟩]
theorem checked41124 : checkPrefixCuts (2^48) 5394137089 10 Manual.Count131072.C041124.packed 64 cuts41124 = true := by
 decide +kernel
def cuts41125 : List PrefixCut := [⟨16,77435433,77435477⟩,
⟨64,302225022,302225202⟩]
theorem checked41125 : checkPrefixCuts (2^48) 5394268161 10 Manual.Count131072.C041125.packed 64 cuts41125 = true := by
 decide +kernel
def pointBounds41125 : List (Nat × Nat × Nat) := [(5394300928,109214646147180,109215031859034)]
theorem point_links_checked41125 : (cuts41125.take 1).map (fun c => (5394268161-1+2*2^10*c.k,109214568711747+c.lower,109214954423557+c.upper)) = pointBounds41125 := by
 decide +kernel
def cuts41126 : List PrefixCut := [⟨35,168119959,168120061⟩,
⟨64,304304846,304305029⟩]
theorem checked41126 : checkPrefixCuts (2^48) 5394399233 10 Manual.Count131072.C041126.packed 64 cuts41126 = true := by
 decide +kernel
def pointBounds41126 : List (Nat × Nat × Nat) := [(5394470912,109215039056728,109215424768820)]
theorem point_links_checked41126 : (cuts41126.take 1).map (fun c => (5394399233-1+2*2^10*c.k,109214870936769+c.lower,109215256648759+c.upper)) = pointBounds41126 := by
 decide +kernel
def cuts41127 : List PrefixCut := [⟨54,255720947,255721100⟩,
⟨64,305601836,305602018⟩]
theorem checked41127 : checkPrefixCuts (2^48) 5394530305 10 Manual.Count131072.C041127.packed 64 cuts41127 = true := by
 decide +kernel
def pointBounds41127 : List (Nat × Nat × Nat) := [(5394640896,109215430962562,109215816674888)]
theorem point_links_checked41127 : (cuts41127.take 1).map (fun c => (5394530305-1+2*2^10*c.k,109215175241615+c.lower,109215560953788+c.upper)) = pointBounds41127 := by
 decide +kernel
def cuts41128 : List PrefixCut := [⟨64,304759603,304759788⟩]
theorem checked41128 : checkPrefixCuts (2^48) 5394661377 10 Manual.Count131072.C041128.packed 64 cuts41128 = true := by
 decide +kernel
def cuts41129 : List PrefixCut := [⟨9,41635815,41635840⟩,
⟨64,304543483,304543662⟩]
theorem checked41129 : checkPrefixCuts (2^48) 5394792449 10 Manual.Count131072.C041129.packed 64 cuts41129 = true := by
 decide +kernel
def pointBounds41129 : List (Nat × Nat × Nat) := [(5394810880,109215827238869,109216212951434)]
theorem point_links_checked41129 : (cuts41129.take 1).map (fun c => (5394792449-1+2*2^10*c.k,109215785603054+c.lower,109216171315594+c.upper)) = pointBounds41129 := by
 decide +kernel
def cuts41130 : List PrefixCut := [⟨28,135390882,135390960⟩,
⟨64,306727404,306727585⟩]
theorem checked41130 : checkPrefixCuts (2^48) 5394923521 10 Manual.Count131072.C041130.packed 64 cuts41130 = true := by
 decide +kernel
def pointBounds41130 : List (Nat × Nat × Nat) := [(5394980864,109216225537419,109216611250216)]
theorem point_links_checked41130 : (cuts41130.take 1).map (fun c => (5394923521-1+2*2^10*c.k,109216090146537+c.lower,109216475859256+c.upper)) = pointBounds41130 := by
 decide +kernel
def cuts41131 : List PrefixCut := [⟨47,223193091,223193225⟩,
⟨64,305780831,305781014⟩]
theorem checked41131 : checkPrefixCuts (2^48) 5395054593 10 Manual.Count131072.C041131.packed 64 cuts41131 = true := by
 decide +kernel
def pointBounds41131 : List (Nat × Nat × Nat) := [(5395150848,109216620067032,109217005780066)]
theorem point_links_checked41131 : (cuts41131.take 1).map (fun c => (5395054593-1+2*2^10*c.k,109216396873941+c.lower,109216782586841+c.upper)) = pointBounds41131 := by
 decide +kernel
def cuts41132 : List PrefixCut := [⟨64,301808399,301808575⟩]
theorem checked41132 : checkPrefixCuts (2^48) 5395185665 10 Manual.Count131072.C041132.packed 64 cuts41132 = true := by
 decide +kernel
def cuts41133 : List PrefixCut := [⟨2,9338467,9338473⟩,
⟨64,303261874,303262053⟩]
theorem checked41133 : checkPrefixCuts (2^48) 5395316737 10 Manual.Count131072.C041133.packed 64 cuts41133 = true := by
 decide +kernel
def pointBounds41133 : List (Nat × Nat × Nat) := [(5395320832,109217013801638,109217399514903)]
theorem point_links_checked41133 : (cuts41133.take 1).map (fun c => (5395316737-1+2*2^10*c.k,109217004463171+c.lower,109217390176430+c.upper)) = pointBounds41133 := by
 decide +kernel
def cuts41134 : List PrefixCut := [⟨21,98546768,98546828⟩,
⟨64,304558660,304558842⟩]
theorem checked41134 : checkPrefixCuts (2^48) 5395447809 10 Manual.Count131072.C041134.packed 64 cuts41134 = true := by
 decide +kernel
def pointBounds41134 : List (Nat × Nat × Nat) := [(5395490816,109217406271813,109217791985311)]
theorem point_links_checked41134 : (cuts41134.take 1).map (fun c => (5395447809-1+2*2^10*c.k,109217307725045+c.lower,109217693438483+c.upper)) = pointBounds41134 := by
 decide +kernel
def cuts41135 : List PrefixCut := [⟨40,189106441,189106552⟩,
⟨64,303194932,303195107⟩]
theorem checked41135 : checkPrefixCuts (2^48) 5395578881 10 Manual.Count131072.C041135.packed 64 cuts41135 = true := by
 decide +kernel
def pointBounds41135 : List (Nat × Nat × Nat) := [(5395660800,109217801390146,109218187103877)]
theorem point_links_checked41135 : (cuts41135.take 1).map (fun c => (5395578881-1+2*2^10*c.k,109217612283705+c.lower,109217997997325+c.upper)) = pointBounds41135 := by
 decide +kernel
def cuts41136 : List PrefixCut := [⟨59,283469182,283469348⟩,
⟨64,307673838,307674018⟩]
theorem checked41136 : checkPrefixCuts (2^48) 5395709953 10 Manual.Count131072.C041136.packed 64 cuts41136 = true := by
 decide +kernel
def pointBounds41136 : List (Nat × Nat × Nat) := [(5395830784,109218198947819,109218584661780)]
theorem point_links_checked41136 : (cuts41136.take 1).map (fun c => (5395709953-1+2*2^10*c.k,109217915478637+c.lower,109218301192432+c.upper)) = pointBounds41136 := by
 decide +kernel
def cuts41137 : List PrefixCut := [⟨64,305318984,305319166⟩]
theorem checked41137 : checkPrefixCuts (2^48) 5395841025 10 Manual.Count131072.C041137.packed 64 cuts41137 = true := by
 decide +kernel
def cuts41138 : List PrefixCut := [⟨14,67186912,67186951⟩,
⟨64,304216127,304216308⟩]
theorem checked41138 : checkPrefixCuts (2^48) 5395972097 10 Manual.Count131072.C041138.packed 64 cuts41138 = true := by
 decide +kernel
def pointBounds41138 : List (Nat × Nat × Nat) := [(5396000768,109218595658371,109218981372567)]
theorem point_links_checked41138 : (cuts41138.take 1).map (fun c => (5395972097-1+2*2^10*c.k,109218528471459+c.lower,109218914185616+c.upper)) = pointBounds41138 := by
 decide +kernel
def cuts41139 : List PrefixCut := [⟨33,157425813,157425909⟩,
⟨64,306868974,306869157⟩]
theorem checked41139 : checkPrefixCuts (2^48) 5396103169 10 Manual.Count131072.C041139.packed 64 cuts41139 = true := by
 decide +kernel
def pointBounds41139 : List (Nat × Nat × Nat) := [(5396170752,109218990113399,109219375827833)]
theorem point_links_checked41139 : (cuts41139.take 1).map (fun c => (5396103169-1+2*2^10*c.k,109218832687586+c.lower,109219218401924+c.upper)) = pointBounds41139 := by
 decide +kernel
def cuts41140 : List PrefixCut := [⟨52,246042679,246042826⟩,
⟨64,304983717,304983897⟩]
theorem checked41140 : checkPrefixCuts (2^48) 5396234241 10 Manual.Count131072.C041140.packed 64 cuts41140 = true := by
 decide +kernel
def pointBounds41140 : List (Nat × Nat × Nat) := [(5396340736,109219385599239,109219771313907)]
theorem point_links_checked41140 : (cuts41140.take 1).map (fun c => (5396234241-1+2*2^10*c.k,109219139556560+c.lower,109219525271081+c.upper)) = pointBounds41140 := by
 decide +kernel
def cuts41141 : List PrefixCut := [⟨64,303515843,303516023⟩]
theorem checked41141 : checkPrefixCuts (2^48) 5396365313 10 Manual.Count131072.C041141.packed 64 cuts41141 = true := by
 decide +kernel
def cuts41142 : List PrefixCut := [⟨7,34216140,34216160⟩,
⟨64,305542691,305542863⟩]
theorem checked41142 : checkPrefixCuts (2^48) 5396496385 10 Manual.Count131072.C041142.packed 64 cuts41142 = true := by
 decide +kernel
def pointBounds41142 : List (Nat × Nat × Nat) := [(5396510720,109219782272260,109220167987161)]
theorem point_links_checked41142 : (cuts41142.take 1).map (fun c => (5396496385-1+2*2^10*c.k,109219748056120+c.lower,109220133771001+c.upper)) = pointBounds41142 := by
 decide +kernel
def cuts41143 : List PrefixCut := [⟨26,120535521,120535594⟩,
⟨64,300476006,300476189⟩]
theorem checked41143 : checkPrefixCuts (2^48) 5396627457 10 Manual.Count131072.C041143.packed 64 cuts41143 = true := by
 decide +kernel
def pointBounds41143 : List (Nat × Nat × Nat) := [(5396680704,109220174134332,109220559849458)]
theorem point_links_checked41143 : (cuts41143.take 1).map (fun c => (5396627457-1+2*2^10*c.k,109220053598811+c.lower,109220439313864+c.upper)) = pointBounds41143 := by
 decide +kernel
def cuts41144 : List PrefixCut := [⟨45,215455791,215455922⟩,
⟨64,305214914,305215094⟩]
theorem checked41144 : checkPrefixCuts (2^48) 5396758529 10 Manual.Count131072.C041144.packed 64 cuts41144 = true := by
 decide +kernel
def pointBounds41144 : List (Nat × Nat × Nat) := [(5396850688,109220569530608,109220955245975)]
theorem point_links_checked41144 : (cuts41144.take 1).map (fun c => (5396758529-1+2*2^10*c.k,109220354074817+c.lower,109220739790053+c.upper)) = pointBounds41144 := by
 decide +kernel
def cuts41145 : List PrefixCut := [⟨64,305051021,305051203⟩]
theorem checked41145 : checkPrefixCuts (2^48) 5396889601 10 Manual.Count131072.C041145.packed 64 cuts41145 = true := by
 decide +kernel
def pointBounds41145 : List (Nat × Nat × Nat) := [(5397020672,109220964340752,109221350056350)]
theorem point_links_checked41145 : (cuts41145.take 1).map (fun c => (5396889601-1+2*2^10*c.k,109220659289731+c.lower,109221045005147+c.upper)) = pointBounds41145 := by
 decide +kernel
def cuts41146 : List PrefixCut := [⟨64,303844067,303844247⟩]
theorem checked41146 : checkPrefixCuts (2^48) 5397020673 10 Manual.Count131072.C041146.packed 64 cuts41146 = true := by
 decide +kernel
def cuts41147 : List PrefixCut := [⟨19,89023972,89024025⟩,
⟨64,304723273,304723457⟩]
theorem checked41147 : checkPrefixCuts (2^48) 5397151745 10 Manual.Count131072.C041147.packed 64 cuts41147 = true := by
 decide +kernel
def pointBounds41147 : List (Nat × Nat × Nat) := [(5397190656,109221357208791,109221742924622)]
theorem point_links_checked41147 : (cuts41147.take 1).map (fun c => (5397151745-1+2*2^10*c.k,109221268184819+c.lower,109221653900597+c.upper)) = pointBounds41147 := by
 decide +kernel
def cuts41148 : List PrefixCut := [⟨38,178512353,178512461⟩,
⟨64,303620713,303620896⟩]
theorem checked41148 : checkPrefixCuts (2^48) 5397282817 10 Manual.Count131072.C041148.packed 64 cuts41148 = true := by
 decide +kernel
def pointBounds41148 : List (Nat × Nat × Nat) := [(5397360640,109221751420445,109222137136515)]
theorem point_links_checked41148 : (cuts41148.take 1).map (fun c => (5397282817-1+2*2^10*c.k,109221572908092+c.lower,109221958624054+c.upper)) = pointBounds41148 := by
 decide +kernel
def cuts41149 : List PrefixCut := [⟨57,269664508,269664670⟩,
⟨64,303300459,303300641⟩]
theorem checked41149 : checkPrefixCuts (2^48) 5397413889 10 Manual.Count131072.C041149.packed 64 cuts41149 = true := by
 decide +kernel
def pointBounds41149 : List (Nat × Nat × Nat) := [(5397530624,109222146193313,109222531909620)]
theorem point_links_checked41149 : (cuts41149.take 1).map (fun c => (5397413889-1+2*2^10*c.k,109221876528805+c.lower,109222262244950+c.upper)) = pointBounds41149 := by
 decide +kernel
def cuts41150 : List PrefixCut := [⟨64,304075321,304075498⟩]
theorem checked41150 : checkPrefixCuts (2^48) 5397544961 10 Manual.Count131072.C041150.packed 64 cuts41150 = true := by
 decide +kernel
def cuts41151 : List PrefixCut := [⟨12,56997006,56997038⟩,
⟨64,304120071,304120249⟩]
theorem checked41151 : checkPrefixCuts (2^48) 5397676033 10 Manual.Count131072.C041151.packed 64 cuts41151 = true := by
 decide +kernel
def pointBounds41151 : List (Nat × Nat × Nat) := [(5397700608,109222540901591,109222926618127)]
theorem point_links_checked41151 : (cuts41151.take 1).map (fun c => (5397676033-1+2*2^10*c.k,109222483904585+c.lower,109222869621089+c.upper)) = pointBounds41151 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000035
