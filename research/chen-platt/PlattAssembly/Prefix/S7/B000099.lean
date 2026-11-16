import PlattAssemblyKernel
import PlattCertificates.Count131072.C063168
import PlattCertificates.Count131072.C063169
import PlattCertificates.Count131072.C063170
import PlattCertificates.Count131072.C063171
import PlattCertificates.Count131072.C063172
import PlattCertificates.Count131072.C063173
import PlattCertificates.Count131072.C063174
import PlattCertificates.Count131072.C063175
import PlattCertificates.Count131072.C063176
import PlattCertificates.Count131072.C063177
import PlattCertificates.Count131072.C063178
import PlattCertificates.Count131072.C063179
import PlattCertificates.Count131072.C063180
import PlattCertificates.Count131072.C063181
import PlattCertificates.Count131072.C063182
import PlattCertificates.Count131072.C063183
import PlattCertificates.Count131072.C063184
import PlattCertificates.Count131072.C063185
import PlattCertificates.Count131072.C063186
import PlattCertificates.Count131072.C063187
import PlattCertificates.Count131072.C063188
import PlattCertificates.Count131072.C063189
import PlattCertificates.Count131072.C063190
import PlattCertificates.Count131072.C063191
import PlattCertificates.Count131072.C063192
import PlattCertificates.Count131072.C063193
import PlattCertificates.Count131072.C063194
import PlattCertificates.Count131072.C063195
import PlattCertificates.Count131072.C063196
import PlattCertificates.Count131072.C063197
import PlattCertificates.Count131072.C063198
import PlattCertificates.Count131072.C063199
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000099
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63168 : List PrefixCut := [⟨64,195384826,195384936⟩]
theorem checked63168 : checkPrefixCuts (2^48) 8283488257 10 Manual.Count131072.C063168.packed 64 cuts63168 = true := by
 decide +kernel
def cuts63169 : List PrefixCut := [⟨8,24941074,24941088⟩,
⟨64,195007949,195008063⟩]
theorem checked63169 : checkPrefixCuts (2^48) 8283619329 10 Manual.Count131072.C063169.packed 64 cuts63169 = true := by
 decide +kernel
def pointBounds63169 : List (Nat × Nat × Nat) := [(8283635712,114551668961205,114552057732360)]
theorem point_links_checked63169 : (cuts63169.take 1).map (fun c => (8283619329-1+2*2^10*c.k,114551644020131+c.lower,114552032791272+c.upper)) = pointBounds63169 := by
 decide +kernel
def cuts63170 : List PrefixCut := [⟨64,195106803,195106918⟩]
theorem checked63170 : checkPrefixCuts (2^48) 8283750401 10 Manual.Count131072.C063170.packed 64 cuts63170 = true := by
 decide +kernel
def cuts63171 : List PrefixCut := [⟨7,21610387,21610399⟩,
⟨64,195715331,195715440⟩]
theorem checked63171 : checkPrefixCuts (2^48) 8283881473 10 Manual.Count131072.C063171.packed 64 cuts63171 = true := by
 decide +kernel
def pointBounds63171 : List (Nat × Nat × Nat) := [(8283895808,114552055745270,114552444516652)]
theorem point_links_checked63171 : (cuts63171.take 1).map (fun c => (8283881473-1+2*2^10*c.k,114552034134883+c.lower,114552422906253+c.upper)) = pointBounds63171 := by
 decide +kernel
def cuts63172 : List PrefixCut := [⟨64,192824114,192824229⟩]
theorem checked63172 : checkPrefixCuts (2^48) 8284012545 10 Manual.Count131072.C063172.packed 64 cuts63172 = true := by
 decide +kernel
def cuts63173 : List PrefixCut := [⟨6,18143998,18144008⟩,
⟨64,195573229,195573339⟩]
theorem checked63173 : checkPrefixCuts (2^48) 8284143617 10 Manual.Count131072.C063173.packed 64 cuts63173 = true := by
 decide +kernel
def pointBounds63173 : List (Nat × Nat × Nat) := [(8284155904,114552440818326,114552829589930)]
theorem point_links_checked63173 : (cuts63173.take 1).map (fun c => (8284143617-1+2*2^10*c.k,114552422674328+c.lower,114552811445922+c.upper)) = pointBounds63173 := by
 decide +kernel
def cuts63174 : List PrefixCut := [⟨64,196657393,196657508⟩]
theorem checked63174 : checkPrefixCuts (2^48) 8284274689 10 Manual.Count131072.C063174.packed 64 cuts63174 = true := by
 decide +kernel
def cuts63175 : List PrefixCut := [⟨5,16512555,16512565⟩,
⟨64,194309931,194310046⟩]
theorem checked63175 : checkPrefixCuts (2^48) 8284405761 10 Manual.Count131072.C063175.packed 64 cuts63175 = true := by
 decide +kernel
def pointBounds63175 : List (Nat × Nat × Nat) := [(8284416000,114552831417505,114553220189334)]
theorem point_links_checked63175 : (cuts63175.take 1).map (fun c => (8284405761-1+2*2^10*c.k,114552814904950+c.lower,114553203676769+c.upper)) = pointBounds63175 := by
 decide +kernel
def cuts63176 : List PrefixCut := [⟨64,198315959,198316075⟩]
theorem checked63176 : checkPrefixCuts (2^48) 8284536833 10 Manual.Count131072.C063176.packed 64 cuts63176 = true := by
 decide +kernel
def cuts63177 : List PrefixCut := [⟨4,12401014,12401022⟩,
⟨64,192910784,192910892⟩]
theorem checked63177 : checkPrefixCuts (2^48) 8284667905 10 Manual.Count131072.C063177.packed 64 cuts63177 = true := by
 decide +kernel
def pointBounds63177 : List (Nat × Nat × Nat) := [(8284676096,114553219931854,114553608703912)]
theorem point_links_checked63177 : (cuts63177.take 1).map (fun c => (8284667905-1+2*2^10*c.k,114553207530840+c.lower,114553596302890+c.upper)) = pointBounds63177 := by
 decide +kernel
def cuts63178 : List PrefixCut := [⟨64,194878266,194878377⟩]
theorem checked63178 : checkPrefixCuts (2^48) 8284798977 10 Manual.Count131072.C063178.packed 64 cuts63178 = true := by
 decide +kernel
def cuts63179 : List PrefixCut := [⟨3,8391655,8391660⟩,
⟨64,192700828,192700940⟩]
theorem checked63179 : checkPrefixCuts (2^48) 8284930049 10 Manual.Count131072.C063179.packed 64 cuts63179 = true := by
 decide +kernel
def pointBounds63179 : List (Nat × Nat × Nat) := [(8284936192,114553603711545,114553992483819)]
theorem point_links_checked63179 : (cuts63179.take 1).map (fun c => (8284930049-1+2*2^10*c.k,114553595319890+c.lower,114553984092159+c.upper)) = pointBounds63179 := by
 decide +kernel
def cuts63180 : List PrefixCut := [⟨64,197589987,197590091⟩]
theorem checked63180 : checkPrefixCuts (2^48) 8285061121 10 Manual.Count131072.C063180.packed 64 cuts63180 = true := by
 decide +kernel
def cuts63181 : List PrefixCut := [⟨2,6047237,6047240⟩,
⟨64,196159991,196160099⟩]
theorem checked63181 : checkPrefixCuts (2^48) 8285192193 10 Manual.Count131072.C063181.packed 64 cuts63181 = true := by
 decide +kernel
def pointBounds63181 : List (Nat × Nat × Nat) := [(8285196288,114553991657942,114554380430430)]
theorem point_links_checked63181 : (cuts63181.take 1).map (fun c => (8285192193-1+2*2^10*c.k,114553985610705+c.lower,114554374383190+c.upper)) = pointBounds63181 := by
 decide +kernel
def cuts63182 : List PrefixCut := [⟨64,193507026,193507137⟩]
theorem checked63182 : checkPrefixCuts (2^48) 8285323265 10 Manual.Count131072.C063182.packed 64 cuts63182 = true := by
 decide +kernel
def cuts63183 : List PrefixCut := [⟨1,3295301,3295302⟩,
⟨64,197274849,197274954⟩]
theorem checked63183 : checkPrefixCuts (2^48) 8285454337 10 Manual.Count131072.C063183.packed 64 cuts63183 = true := by
 decide +kernel
def pointBounds63183 : List (Nat × Nat × Nat) := [(8285456384,114554378573023,114554767345728)]
theorem point_links_checked63183 : (cuts63183.take 1).map (fun c => (8285454337-1+2*2^10*c.k,114554375277722+c.lower,114554764050426+c.upper)) = pointBounds63183 := by
 decide +kernel
def cuts63184 : List PrefixCut := [⟨64,193195177,193195288⟩]
theorem checked63184 : checkPrefixCuts (2^48) 8285585409 10 Manual.Count131072.C063184.packed 64 cuts63184 = true := by
 decide +kernel
def pointBounds63184 : List (Nat × Nat × Nat) := [(8285716480,114554765747748,114555154520668)]
theorem point_links_checked63184 : (cuts63184.take 1).map (fun c => (8285585409-1+2*2^10*c.k,114554572552571+c.lower,114554961325380+c.upper)) = pointBounds63184 := by
 decide +kernel
def cuts63185 : List PrefixCut := [⟨64,197710238,197710350⟩]
theorem checked63185 : checkPrefixCuts (2^48) 8285716481 10 Manual.Count131072.C063185.packed 64 cuts63185 = true := by
 decide +kernel
def cuts63186 : List PrefixCut := [⟨63,190437472,190437583⟩,
⟨64,193664625,193664738⟩]
theorem checked63186 : checkPrefixCuts (2^48) 8285847553 10 Manual.Count131072.C063186.packed 64 cuts63186 = true := by
 decide +kernel
def pointBounds63186 : List (Nat × Nat × Nat) := [(8285976576,114555153895458,114555542668601)]
theorem point_links_checked63186 : (cuts63186.take 1).map (fun c => (8285847553-1+2*2^10*c.k,114554963457986+c.lower,114555352231018+c.upper)) = pointBounds63186 := by
 decide +kernel
def cuts63187 : List PrefixCut := [⟨64,195258152,195258263⟩]
theorem checked63187 : checkPrefixCuts (2^48) 8285978625 10 Manual.Count131072.C063187.packed 64 cuts63187 = true := by
 decide +kernel
def cuts63188 : List PrefixCut := [⟨62,188291417,188291522⟩,
⟨64,194711551,194711658⟩]
theorem checked63188 : checkPrefixCuts (2^48) 8286109697 10 Manual.Count131072.C063188.packed 64 cuts63188 = true := by
 decide +kernel
def pointBounds63188 : List (Nat × Nat × Nat) := [(8286236672,114555540672180,114555929445541)]
theorem point_links_checked63188 : (cuts63188.take 1).map (fun c => (8286109697-1+2*2^10*c.k,114555352380763+c.lower,114555741154019+c.upper)) = pointBounds63188 := by
 decide +kernel
def cuts63189 : List PrefixCut := [⟨64,195625640,195625751⟩]
theorem checked63189 : checkPrefixCuts (2^48) 8286240769 10 Manual.Count131072.C063189.packed 64 cuts63189 = true := by
 decide +kernel
def cuts63190 : List PrefixCut := [⟨61,183156305,183156412⟩,
⟨64,192735249,192735362⟩]
theorem checked63190 : checkPrefixCuts (2^48) 8286371841 10 Manual.Count131072.C063190.packed 64 cuts63190 = true := by
 decide +kernel
def pointBounds63190 : List (Nat × Nat × Nat) := [(8286496768,114555925874259,114556314647840)]
theorem point_links_checked63190 : (cuts63190.take 1).map (fun c => (8286371841-1+2*2^10*c.k,114555742717954+c.lower,114556131491428+c.upper)) = pointBounds63190 := by
 decide +kernel
def cuts63191 : List PrefixCut := [⟨64,194668354,194668459⟩]
theorem checked63191 : checkPrefixCuts (2^48) 8286502913 10 Manual.Count131072.C063191.packed 64 cuts63191 = true := by
 decide +kernel
def cuts63192 : List PrefixCut := [⟨60,180399194,180399298⟩,
⟨64,192355513,192355625⟩]
theorem checked63192 : checkPrefixCuts (2^48) 8286633985 10 Manual.Count131072.C063192.packed 64 cuts63192 = true := by
 decide +kernel
def pointBounds63192 : List (Nat × Nat × Nat) := [(8286756864,114556310520751,114556699294547)]
theorem point_links_checked63192 : (cuts63192.take 1).map (fun c => (8286633985-1+2*2^10*c.k,114556130121557+c.lower,114556518895249+c.upper)) = pointBounds63192 := by
 decide +kernel
def cuts63193 : List PrefixCut := [⟨64,195851013,195851129⟩]
theorem checked63193 : checkPrefixCuts (2^48) 8286765057 10 Manual.Count131072.C063193.packed 64 cuts63193 = true := by
 decide +kernel
def cuts63194 : List PrefixCut := [⟨59,181344550,181344654⟩,
⟨64,196459308,196459419⟩]
theorem checked63194 : checkPrefixCuts (2^48) 8286896129 10 Manual.Count131072.C063194.packed 64 cuts63194 = true := by
 decide +kernel
def pointBounds63194 : List (Nat × Nat × Nat) := [(8287016960,114556699672633,114557088446657)]
theorem point_links_checked63194 : (cuts63194.take 1).map (fun c => (8286896129-1+2*2^10*c.k,114556518328083+c.lower,114556907102003+c.upper)) = pointBounds63194 := by
 decide +kernel
def cuts63195 : List PrefixCut := [⟨64,199479137,199479252⟩]
theorem checked63195 : checkPrefixCuts (2^48) 8287027201 10 Manual.Count131072.C063195.packed 64 cuts63195 = true := by
 decide +kernel
def cuts63196 : List PrefixCut := [⟨58,176787531,176787629⟩,
⟨64,194211411,194211517⟩]
theorem checked63196 : checkPrefixCuts (2^48) 8287158273 10 Manual.Count131072.C063196.packed 64 cuts63196 = true := by
 decide +kernel
def pointBounds63196 : List (Nat × Nat × Nat) := [(8287277056,114557091054059,114557479828303)]
theorem point_links_checked63196 : (cuts63196.take 1).map (fun c => (8287158273-1+2*2^10*c.k,114556914266528+c.lower,114557303040674+c.upper)) = pointBounds63196 := by
 decide +kernel
def cuts63197 : List PrefixCut := [⟨64,195397100,195397211⟩]
theorem checked63197 : checkPrefixCuts (2^48) 8287289345 10 Manual.Count131072.C063197.packed 64 cuts63197 = true := by
 decide +kernel
def cuts63198 : List PrefixCut := [⟨57,172162881,172162985⟩,
⟨64,193899590,193899707⟩]
theorem checked63198 : checkPrefixCuts (2^48) 8287420417 10 Manual.Count131072.C063198.packed 64 cuts63198 = true := by
 decide +kernel
def pointBounds63198 : List (Nat × Nat × Nat) := [(8287537152,114557476037920,114557864812387)]
theorem point_links_checked63198 : (cuts63198.take 1).map (fun c => (8287420417-1+2*2^10*c.k,114557303875039+c.lower,114557692649402+c.upper)) = pointBounds63198 := by
 decide +kernel
def cuts63199 : List PrefixCut := [⟨64,193828592,193828706⟩]
theorem checked63199 : checkPrefixCuts (2^48) 8287551489 10 Manual.Count131072.C063199.packed 64 cuts63199 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000099
