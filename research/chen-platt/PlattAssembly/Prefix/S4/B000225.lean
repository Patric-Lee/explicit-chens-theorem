import PlattAssemblyKernel
import PlattCertificates.Count131072.C037200
import PlattCertificates.Count131072.C037201
import PlattCertificates.Count131072.C037202
import PlattCertificates.Count131072.C037203
import PlattCertificates.Count131072.C037204
import PlattCertificates.Count131072.C037205
import PlattCertificates.Count131072.C037206
import PlattCertificates.Count131072.C037207
import PlattCertificates.Count131072.C037208
import PlattCertificates.Count131072.C037209
import PlattCertificates.Count131072.C037210
import PlattCertificates.Count131072.C037211
import PlattCertificates.Count131072.C037212
import PlattCertificates.Count131072.C037213
import PlattCertificates.Count131072.C037214
import PlattCertificates.Count131072.C037215
import PlattCertificates.Count131072.C037216
import PlattCertificates.Count131072.C037217
import PlattCertificates.Count131072.C037218
import PlattCertificates.Count131072.C037219
import PlattCertificates.Count131072.C037220
import PlattCertificates.Count131072.C037221
import PlattCertificates.Count131072.C037222
import PlattCertificates.Count131072.C037223
import PlattCertificates.Count131072.C037224
import PlattCertificates.Count131072.C037225
import PlattCertificates.Count131072.C037226
import PlattCertificates.Count131072.C037227
import PlattCertificates.Count131072.C037228
import PlattCertificates.Count131072.C037229
import PlattCertificates.Count131072.C037230
import PlattCertificates.Count131072.C037231
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000225
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts37200 : List PrefixCut := [⟨35,184291088,184291198⟩,
⟨64,338874349,338874552⟩]
theorem checked37200 : checkPrefixCuts (2^48) 4879810561 10 Manual.Count131072.C037200.packed 64 cuts37200 = true := by
 decide +kernel
def pointBounds37200 : List (Nat × Nat × Nat) := [(4879882240,107952963525235,107953348481807)]
theorem point_links_checked37200 : (cuts37200.take 1).map (fun c => (4879810561-1+2*2^10*c.k,107952779234147+c.lower,107953164190609+c.upper)) = pointBounds37200 := by
 decide +kernel
def cuts37201 : List PrefixCut := [⟨46,243637839,243637986⟩,
⟨64,340480272,340480480⟩]
theorem checked37201 : checkPrefixCuts (2^48) 4879941633 10 Manual.Count131072.C037201.packed 64 cuts37201 = true := by
 decide +kernel
def pointBounds37201 : List (Nat × Nat × Nat) := [(4880035840,107953361746335,107953746703147)]
theorem point_links_checked37201 : (cuts37201.take 1).map (fun c => (4879941633-1+2*2^10*c.k,107953118108496+c.lower,107953503065161+c.upper)) = pointBounds37201 := by
 decide +kernel
def cuts37202 : List PrefixCut := [⟨57,305922696,305922881⟩,
⟨64,344681610,344681819⟩]
theorem checked37202 : checkPrefixCuts (2^48) 4880072705 10 Manual.Count131072.C037202.packed 64 cuts37202 = true := by
 decide +kernel
def pointBounds37202 : List (Nat × Nat × Nat) := [(4880189440,107953764511464,107954149468522)]
theorem point_links_checked37202 : (cuts37202.take 1).map (fun c => (4880072705-1+2*2^10*c.k,107953458588768+c.lower,107953843545641+c.upper)) = pointBounds37202 := by
 decide +kernel
def cuts37203 : List PrefixCut := [⟨64,337405192,337405393⟩]
theorem checked37203 : checkPrefixCuts (2^48) 4880203777 10 Manual.Count131072.C037203.packed 64 cuts37203 = true := by
 decide +kernel
def cuts37204 : List PrefixCut := [⟨4,19724943,19724956⟩,
⟨64,336473312,336473520⟩]
theorem checked37204 : checkPrefixCuts (2^48) 4880334849 10 Manual.Count131072.C037204.packed 64 cuts37204 = true := by
 decide +kernel
def pointBounds37204 : List (Nat × Nat × Nat) := [(4880343040,107954160400513,107954545357809)]
theorem point_links_checked37204 : (cuts37204.take 1).map (fun c => (4880334849-1+2*2^10*c.k,107954140675570+c.lower,107954525632853+c.upper)) = pointBounds37204 := by
 decide +kernel
def cuts37205 : List PrefixCut := [⟨15,80800702,80800749⟩,
⟨64,346095660,346095863⟩]
theorem checked37205 : checkPrefixCuts (2^48) 4880465921 10 Manual.Count131072.C037205.packed 64 cuts37205 = true := by
 decide +kernel
def pointBounds37205 : List (Nat × Nat × Nat) := [(4880496640,107954557949584,107954942907122)]
theorem point_links_checked37205 : (cuts37205.take 1).map (fun c => (4880465921-1+2*2^10*c.k,107954477148882+c.lower,107954862106373+c.upper)) = pointBounds37205 := by
 decide +kernel
def cuts37206 : List PrefixCut := [⟨26,137143810,137143895⟩,
⟨64,338300730,338300939⟩]
theorem checked37206 : checkPrefixCuts (2^48) 4880596993 10 Manual.Count131072.C037206.packed 64 cuts37206 = true := by
 decide +kernel
def pointBounds37206 : List (Nat × Nat × Nat) := [(4880650240,107954960388352,107955345346131)]
theorem point_links_checked37206 : (cuts37206.take 1).map (fun c => (4880596993-1+2*2^10*c.k,107954823244542+c.lower,107955208202236+c.upper)) = pointBounds37206 := by
 decide +kernel
def cuts37207 : List PrefixCut := [⟨37,197289860,197289983⟩,
⟨64,339906425,339906635⟩]
theorem checked37207 : checkPrefixCuts (2^48) 4880728065 10 Manual.Count131072.C037207.packed 64 cuts37207 = true := by
 decide +kernel
def pointBounds37207 : List (Nat × Nat × Nat) := [(4880803840,107955358835132,107955743793158)]
theorem point_links_checked37207 : (cuts37207.take 1).map (fun c => (4880728065-1+2*2^10*c.k,107955161545272+c.lower,107955546503175+c.upper)) = pointBounds37207 := by
 decide +kernel
def cuts37208 : List PrefixCut := [⟨48,255759995,255760155⟩,
⟨64,342665330,342665544⟩]
theorem checked37208 : checkPrefixCuts (2^48) 4880859137 10 Manual.Count131072.C037208.packed 64 cuts37208 = true := by
 decide +kernel
def pointBounds37208 : List (Nat × Nat × Nat) := [(4880957440,107955757211692,107956142169965)]
theorem point_links_checked37208 : (cuts37208.take 1).map (fun c => (4880859137-1+2*2^10*c.k,107955501451697+c.lower,107955886409810+c.upper)) = pointBounds37208 := by
 decide +kernel
def cuts37209 : List PrefixCut := [⟨59,309152049,309152239⟩,
⟨64,336716443,336716648⟩]
theorem checked37209 : checkPrefixCuts (2^48) 4880990209 10 Manual.Count131072.C037209.packed 64 cuts37209 = true := by
 decide +kernel
def pointBounds37209 : List (Nat × Nat × Nat) := [(4881111040,107956153269076,107956538227593)]
theorem point_links_checked37209 : (cuts37209.take 1).map (fun c => (4880990209-1+2*2^10*c.k,107955844117027+c.lower,107956229075354+c.upper)) = pointBounds37209 := by
 decide +kernel
def cuts37210 : List PrefixCut := [⟨64,333420554,333420757⟩]
theorem checked37210 : checkPrefixCuts (2^48) 4881121281 10 Manual.Count131072.C037210.packed 64 cuts37210 = true := by
 decide +kernel
def cuts37211 : List PrefixCut := [⟨6,31888417,31888438⟩,
⟨64,338024681,338024886⟩]
theorem checked37211 : checkPrefixCuts (2^48) 4881252353 10 Manual.Count131072.C037211.packed 64 cuts37211 = true := by
 decide +kernel
def pointBounds37211 : List (Nat × Nat × Nat) := [(4881264640,107956546142441,107956931101197)]
theorem point_links_checked37211 : (cuts37211.take 1).map (fun c => (4881252353-1+2*2^10*c.k,107956514254024+c.lower,107956899212759+c.upper)) = pointBounds37211 := by
 decide +kernel
def cuts37212 : List PrefixCut := [⟨17,91337759,91337815⟩,
⟨64,344243092,344243296⟩]
theorem checked37212 : checkPrefixCuts (2^48) 4881383425 10 Manual.Count131072.C037212.packed 64 cuts37212 = true := by
 decide +kernel
def pointBounds37212 : List (Nat × Nat × Nat) := [(4881418240,107956943616464,107957328575460)]
theorem point_links_checked37212 : (cuts37212.take 1).map (fun c => (4881383425-1+2*2^10*c.k,107956852278705+c.lower,107957237237645+c.upper)) = pointBounds37212 := by
 decide +kernel
def cuts37213 : List PrefixCut := [⟨28,145536482,145536570⟩,
⟨64,333566629,333566834⟩]
theorem checked37213 : checkPrefixCuts (2^48) 4881514497 10 Manual.Count131072.C037213.packed 64 cuts37213 = true := by
 decide +kernel
def pointBounds37213 : List (Nat × Nat × Nat) := [(4881571840,107957342058279,107957727017511)]
theorem point_links_checked37213 : (cuts37213.take 1).map (fun c => (4881514497-1+2*2^10*c.k,107957196521797+c.lower,107957581480941+c.upper)) = pointBounds37213 := by
 decide +kernel
def cuts37214 : List PrefixCut := [⟨39,212301783,212301908⟩,
⟨64,346127375,346127585⟩]
theorem checked37214 : checkPrefixCuts (2^48) 4881645569 10 Manual.Count131072.C037214.packed 64 cuts37214 = true := by
 decide +kernel
def pointBounds37214 : List (Nat × Nat × Nat) := [(4881725440,107957742390209,107958127349683)]
theorem point_links_checked37214 : (cuts37214.take 1).map (fun c => (4881645569-1+2*2^10*c.k,107957530088426+c.lower,107957915047775+c.upper)) = pointBounds37214 := by
 decide +kernel
def cuts37215 : List PrefixCut := [⟨50,262169487,262169654⟩,
⟨64,335855022,335855232⟩]
theorem checked37215 : checkPrefixCuts (2^48) 4881776641 10 Manual.Count131072.C037215.packed 64 cuts37215 = true := by
 decide +kernel
def pointBounds37215 : List (Nat × Nat × Nat) := [(4881879040,107958138385288,107958523345014)]
theorem point_links_checked37215 : (cuts37215.take 1).map (fun c => (4881776641-1+2*2^10*c.k,107957876215801+c.lower,107958261175360+c.upper)) = pointBounds37215 := by
 decide +kernel
def cuts37216 : List PrefixCut := [⟨61,323623147,323623347⟩,
⟨64,338382887,338383096⟩]
theorem checked37216 : checkPrefixCuts (2^48) 4881907713 10 Manual.Count131072.C037216.packed 64 cuts37216 = true := by
 decide +kernel
def pointBounds37216 : List (Nat × Nat × Nat) := [(4882032640,107958535693970,107958920653939)]
theorem point_links_checked37216 : (cuts37216.take 1).map (fun c => (4881907713-1+2*2^10*c.k,107958212070823+c.lower,107958597030592+c.upper)) = pointBounds37216 := by
 decide +kernel
def cuts37217 : List PrefixCut := [⟨64,342294284,342294494⟩]
theorem checked37217 : checkPrefixCuts (2^48) 4882038785 10 Manual.Count131072.C037217.packed 64 cuts37217 = true := by
 decide +kernel
def cuts37218 : List PrefixCut := [⟨8,42375358,42375384⟩,
⟨64,334617247,334617453⟩]
theorem checked37218 : checkPrefixCuts (2^48) 4882169857 10 Manual.Count131072.C037218.packed 64 cuts37218 = true := by
 decide +kernel
def pointBounds37218 : List (Nat × Nat × Nat) := [(4882186240,107958935123352,107959320083566)]
theorem point_links_checked37218 : (cuts37218.take 1).map (fun c => (4882169857-1+2*2^10*c.k,107958892747994+c.lower,107959277708182+c.upper)) = pointBounds37218 := by
 decide +kernel
def cuts37219 : List PrefixCut := [⟨19,102389715,102389779⟩,
⟨64,341987668,341987876⟩]
theorem checked37219 : checkPrefixCuts (2^48) 4882300929 10 Manual.Count131072.C037219.packed 64 cuts37219 = true := by
 decide +kernel
def pointBounds37219 : List (Nat × Nat × Nat) := [(4882339840,107959329754956,107959714715414)]
theorem point_links_checked37219 : (cuts37219.take 1).map (fun c => (4882300929-1+2*2^10*c.k,107959227365241+c.lower,107959612325635+c.upper)) = pointBounds37219 := by
 decide +kernel
def cuts37220 : List PrefixCut := [⟨30,156693211,156693305⟩,
⟨64,335809943,335810146⟩]
theorem checked37220 : checkPrefixCuts (2^48) 4882432001 10 Manual.Count131072.C037220.packed 64 cuts37220 = true := by
 decide +kernel
def pointBounds37220 : List (Nat × Nat × Nat) := [(4882493440,107959726046120,107960111006816)]
theorem point_links_checked37220 : (cuts37220.take 1).map (fun c => (4882432001-1+2*2^10*c.k,107959569352909+c.lower,107959954313511+c.upper)) = pointBounds37220 := by
 decide +kernel
def cuts37221 : List PrefixCut := [⟨41,215836014,215836149⟩,
⟨64,340182174,340182382⟩]
theorem checked37221 : checkPrefixCuts (2^48) 4882563073 10 Manual.Count131072.C037221.packed 64 cuts37221 = true := by
 decide +kernel
def pointBounds37221 : List (Nat × Nat × Nat) := [(4882647040,107960120998866,107960505959806)]
theorem point_links_checked37221 : (cuts37221.take 1).map (fun c => (4882563073-1+2*2^10*c.k,107959905162852+c.lower,107960290123657+c.upper)) = pointBounds37221 := by
 decide +kernel
def cuts37222 : List PrefixCut := [⟨52,276070635,276070802⟩,
⟨64,339423649,339423853⟩]
theorem checked37222 : checkPrefixCuts (2^48) 4882694145 10 Manual.Count131072.C037222.packed 64 cuts37222 = true := by
 decide +kernel
def pointBounds37222 : List (Nat × Nat × Nat) := [(4882800640,107960521415661,107960906376841)]
theorem point_links_checked37222 : (cuts37222.take 1).map (fun c => (4882694145-1+2*2^10*c.k,107960245345026+c.lower,107960630306039+c.upper)) = pointBounds37222 := by
 decide +kernel
def cuts37223 : List PrefixCut := [⟨63,333246604,333246808⟩,
⟨64,338319309,338319516⟩]
theorem checked37223 : checkPrefixCuts (2^48) 4882825217 10 Manual.Count131072.C037223.packed 64 cuts37223 = true := by
 decide +kernel
def pointBounds37223 : List (Nat × Nat × Nat) := [(4882954240,107960918015279,107961302976700)]
theorem point_links_checked37223 : (cuts37223.take 1).map (fun c => (4882825217-1+2*2^10*c.k,107960584768675+c.lower,107960969729892+c.upper)) = pointBounds37223 := by
 decide +kernel
def cuts37224 : List PrefixCut := [⟨64,336638567,336638775⟩]
theorem checked37224 : checkPrefixCuts (2^48) 4882956289 10 Manual.Count131072.C037224.packed 64 cuts37224 = true := by
 decide +kernel
def cuts37225 : List PrefixCut := [⟨10,52570138,52570170⟩,
⟨64,339453941,339454150⟩]
theorem checked37225 : checkPrefixCuts (2^48) 4883087361 10 Manual.Count131072.C037225.packed 64 cuts37225 = true := by
 decide +kernel
def pointBounds37225 : List (Nat × Nat × Nat) := [(4883107840,107961312296689,107961697258353)]
theorem point_links_checked37225 : (cuts37225.take 1).map (fun c => (4883087361-1+2*2^10*c.k,107961259726551+c.lower,107961644688183+c.upper)) = pointBounds37225 := by
 decide +kernel
def cuts37226 : List PrefixCut := [⟨21,109690837,109690907⟩,
⟨64,335640566,335640771⟩]
theorem checked37226 : checkPrefixCuts (2^48) 4883218433 10 Manual.Count131072.C037226.packed 64 cuts37226 = true := by
 decide +kernel
def pointBounds37226 : List (Nat × Nat × Nat) := [(4883261440,107961708871329,107962093833240)]
theorem point_links_checked37226 : (cuts37226.take 1).map (fun c => (4883218433-1+2*2^10*c.k,107961599180492+c.lower,107961984142333+c.upper)) = pointBounds37226 := by
 decide +kernel
def cuts37227 : List PrefixCut := [⟨32,171015901,171016005⟩,
⟨64,341164921,341165131⟩]
theorem checked37227 : checkPrefixCuts (2^48) 4883349505 10 Manual.Count131072.C037227.packed 64 cuts37227 = true := by
 decide +kernel
def pointBounds37227 : List (Nat × Nat × Nat) := [(4883415040,107962105836959,107962490799109)]
theorem point_links_checked37227 : (cuts37227.take 1).map (fun c => (4883349505-1+2*2^10*c.k,107961934821058+c.lower,107962319783104+c.upper)) = pointBounds37227 := by
 decide +kernel
def cuts37228 : List PrefixCut := [⟨43,229686062,229686199⟩,
⟨64,344037627,344037833⟩]
theorem checked37228 : checkPrefixCuts (2^48) 4883480577 10 Manual.Count131072.C037228.packed 64 cuts37228 = true := by
 decide +kernel
def pointBounds37228 : List (Nat × Nat × Nat) := [(4883568640,107962505672041,107962890634434)]
theorem point_links_checked37228 : (cuts37228.take 1).map (fun c => (4883480577-1+2*2^10*c.k,107962275985979+c.lower,107962660948235+c.upper)) = pointBounds37228 := by
 decide +kernel
def cuts37229 : List PrefixCut := [⟨54,287488197,287488370⟩,
⟨64,339532779,339532985⟩]
theorem checked37229 : checkPrefixCuts (2^48) 4883611649 10 Manual.Count131072.C037229.packed 64 cuts37229 = true := by
 decide +kernel
def pointBounds37229 : List (Nat × Nat × Nat) := [(4883722240,107962907511803,107963292474438)]
theorem point_links_checked37229 : (cuts37229.take 1).map (fun c => (4883611649-1+2*2^10*c.k,107962620023606+c.lower,107963004986068+c.upper)) = pointBounds37229 := by
 decide +kernel
def cuts37230 : List PrefixCut := [⟨64,338025182,338025393⟩]
theorem checked37230 : checkPrefixCuts (2^48) 4883742721 10 Manual.Count131072.C037230.packed 64 cuts37230 = true := by
 decide +kernel
def cuts37231 : List PrefixCut := [⟨1,5359917,5359921⟩,
⟨64,337958487,337958695⟩]
theorem checked37231 : checkPrefixCuts (2^48) 4883873793 10 Manual.Count131072.C037231.packed 64 cuts37231 = true := by
 decide +kernel
def pointBounds37231 : List (Nat × Nat × Nat) := [(4883875840,107963302941484,107963687904367)]
theorem point_links_checked37231 : (cuts37231.take 1).map (fun c => (4883873793-1+2*2^10*c.k,107963297581567+c.lower,107963682544446+c.upper)) = pointBounds37231 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000225
