import PlattAssemblyKernel
import PlattCertificates.Count131072.C071216
import PlattCertificates.Count131072.C071217
import PlattCertificates.Count131072.C071218
import PlattCertificates.Count131072.C071219
import PlattCertificates.Count131072.C071220
import PlattCertificates.Count131072.C071221
import PlattCertificates.Count131072.C071222
import PlattCertificates.Count131072.C071223
import PlattCertificates.Count131072.C071224
import PlattCertificates.Count131072.C071225
import PlattCertificates.Count131072.C071226
import PlattCertificates.Count131072.C071227
import PlattCertificates.Count131072.C071228
import PlattCertificates.Count131072.C071229
import PlattCertificates.Count131072.C071230
import PlattCertificates.Count131072.C071231
import PlattCertificates.Count131072.C071232
import PlattCertificates.Count131072.C071233
import PlattCertificates.Count131072.C071234
import PlattCertificates.Count131072.C071235
import PlattCertificates.Count131072.C071236
import PlattCertificates.Count131072.C071237
import PlattCertificates.Count131072.C071238
import PlattCertificates.Count131072.C071239
import PlattCertificates.Count131072.C071240
import PlattCertificates.Count131072.C071241
import PlattCertificates.Count131072.C071242
import PlattCertificates.Count131072.C071243
import PlattCertificates.Count131072.C071244
import PlattCertificates.Count131072.C071245
import PlattCertificates.Count131072.C071246
import PlattCertificates.Count131072.C071247
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000038
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71216 : List PrefixCut := [⟨64,170963111,170963214⟩]
theorem checked71216 : checkPrefixCuts (2^48) 9338355713 10 Manual.Count131072.C071216.packed 64 cuts71216 = true := by
 decide +kernel
def cuts71217 : List PrefixCut := [⟨64,171382689,171382794⟩]
theorem checked71217 : checkPrefixCuts (2^48) 9338486785 10 Manual.Count131072.C071217.packed 64 cuts71217 = true := by
 decide +kernel
def cuts71218 : List PrefixCut := [⟨15,40810789,40810815⟩,
⟨64,173550419,173550523⟩]
theorem checked71218 : checkPrefixCuts (2^48) 9338617857 10 Manual.Count131072.C071218.packed 64 cuts71218 = true := by
 decide +kernel
def pointBounds71218 : List (Nat × Nat × Nat) := [(9338648576,116025305331988,116025694962007)]
theorem point_links_checked71218 : (cuts71218.take 1).map (fun c => (9338617857-1+2*2^10*c.k,116025264521199+c.lower,116025654151192+c.upper)) = pointBounds71218 := by
 decide +kernel
def cuts71219 : List PrefixCut := [⟨64,170232550,170232651⟩]
theorem checked71219 : checkPrefixCuts (2^48) 9338748929 10 Manual.Count131072.C071219.packed 64 cuts71219 = true := by
 decide +kernel
def cuts71220 : List PrefixCut := [⟨30,81468455,81468502⟩,
⟨64,172972893,172972992⟩]
theorem checked71220 : checkPrefixCuts (2^48) 9338880001 10 Manual.Count131072.C071220.packed 64 cuts71220 = true := by
 decide +kernel
def pointBounds71220 : List (Nat × Nat × Nat) := [(9338941440,116025689772623,116026079402868)]
theorem point_links_checked71220 : (cuts71220.take 1).map (fun c => (9338880001-1+2*2^10*c.k,116025608304168+c.lower,116025997934366+c.upper)) = pointBounds71220 := by
 decide +kernel
def cuts71221 : List PrefixCut := [⟨64,171463490,171463589⟩]
theorem checked71221 : checkPrefixCuts (2^48) 9339011073 10 Manual.Count131072.C071221.packed 64 cuts71221 = true := by
 decide +kernel
def cuts71222 : List PrefixCut := [⟨45,121581202,121581276⟩,
⟨64,174083179,174083278⟩]
theorem checked71222 : checkPrefixCuts (2^48) 9339142145 10 Manual.Count131072.C071222.packed 64 cuts71222 = true := by
 decide +kernel
def pointBounds71222 : List (Nat × Nat × Nat) := [(9339234304,116026074321753,116026463952223)]
theorem point_links_checked71222 : (cuts71222.take 1).map (fun c => (9339142145-1+2*2^10*c.k,116025952740551+c.lower,116026342370947+c.upper)) = pointBounds71222 := by
 decide +kernel
def cuts71223 : List PrefixCut := [⟨64,170132574,170132681⟩]
theorem checked71223 : checkPrefixCuts (2^48) 9339273217 10 Manual.Count131072.C071223.packed 64 cuts71223 = true := by
 decide +kernel
def cuts71224 : List PrefixCut := [⟨60,160576448,160576545⟩,
⟨64,171456270,171456374⟩]
theorem checked71224 : checkPrefixCuts (2^48) 9339404289 10 Manual.Count131072.C071224.packed 64 cuts71224 = true := by
 decide +kernel
def pointBounds71224 : List (Nat × Nat × Nat) := [(9339527168,116026457532752,116026847163451)]
theorem point_links_checked71224 : (cuts71224.take 1).map (fun c => (9339404289-1+2*2^10*c.k,116026296956304+c.lower,116026686586906+c.upper)) = pointBounds71224 := by
 decide +kernel
def cuts71225 : List PrefixCut := [⟨64,173593636,173593740⟩]
theorem checked71225 : checkPrefixCuts (2^48) 9339535361 10 Manual.Count131072.C071225.packed 64 cuts71225 = true := by
 decide +kernel
def cuts71226 : List PrefixCut := [⟨64,170004863,170004973⟩]
theorem checked71226 : checkPrefixCuts (2^48) 9339666433 10 Manual.Count131072.C071226.packed 64 cuts71226 = true := by
 decide +kernel
def cuts71227 : List PrefixCut := [⟨11,29745332,29745352⟩,
⟨64,171931239,171931338⟩]
theorem checked71227 : checkPrefixCuts (2^48) 9339797505 10 Manual.Count131072.C071227.packed 64 cuts71227 = true := by
 decide +kernel
def pointBounds71227 : List (Nat × Nat × Nat) := [(9339820032,116026841756405,116027231387345)]
theorem point_links_checked71227 : (cuts71227.take 1).map (fun c => (9339797505-1+2*2^10*c.k,116026812011073+c.lower,116027201641993+c.upper)) = pointBounds71227 := by
 decide +kernel
def cuts71228 : List PrefixCut := [⟨64,170271305,170271411⟩]
theorem checked71228 : checkPrefixCuts (2^48) 9339928577 10 Manual.Count131072.C071228.packed 64 cuts71228 = true := by
 decide +kernel
def cuts71229 : List PrefixCut := [⟨26,70639298,70639340⟩,
⟨64,174216755,174216862⟩]
theorem checked71229 : checkPrefixCuts (2^48) 9340059649 10 Manual.Count131072.C071229.packed 64 cuts71229 = true := by
 decide +kernel
def pointBounds71229 : List (Nat × Nat × Nat) := [(9340112896,116027224852915,116027614484082)]
theorem point_links_checked71229 : (cuts71229.take 1).map (fun c => (9340059649-1+2*2^10*c.k,116027154213617+c.lower,116027543844742+c.upper)) = pointBounds71229 := by
 decide +kernel
def cuts71230 : List PrefixCut := [⟨64,174003364,174003470⟩]
theorem checked71230 : checkPrefixCuts (2^48) 9340190721 10 Manual.Count131072.C071230.packed 64 cuts71230 = true := by
 decide +kernel
def cuts71231 : List PrefixCut := [⟨41,111591101,111591167⟩,
⟨64,173940653,173940753⟩]
theorem checked71231 : checkPrefixCuts (2^48) 9340321793 10 Manual.Count131072.C071231.packed 64 cuts71231 = true := by
 decide +kernel
def pointBounds71231 : List (Nat × Nat × Nat) := [(9340405760,116027614024837,116028003656241)]
theorem point_links_checked71231 : (cuts71231.take 1).map (fun c => (9340321793-1+2*2^10*c.k,116027502433736+c.lower,116027892065074+c.upper)) = pointBounds71231 := by
 decide +kernel
def cuts71232 : List PrefixCut := [⟨64,171437023,171437127⟩]
theorem checked71232 : checkPrefixCuts (2^48) 9340452865 10 Manual.Count131072.C071232.packed 64 cuts71232 = true := by
 decide +kernel
def cuts71233 : List PrefixCut := [⟨56,149496902,149496992⟩,
⟨64,171012734,171012837⟩]
theorem checked71233 : checkPrefixCuts (2^48) 9340583937 10 Manual.Count131072.C071233.packed 64 cuts71233 = true := by
 decide +kernel
def pointBounds71233 : List (Nat × Nat × Nat) := [(9340698624,116027997308314,116028386939946)]
theorem point_links_checked71233 : (cuts71233.take 1).map (fun c => (9340583937-1+2*2^10*c.k,116027847811412+c.lower,116028237442954+c.upper)) = pointBounds71233 := by
 decide +kernel
def cuts71234 : List PrefixCut := [⟨64,170437785,170437882⟩]
theorem checked71234 : checkPrefixCuts (2^48) 9340715009 10 Manual.Count131072.C071234.packed 64 cuts71234 = true := by
 decide +kernel
def cuts71235 : List PrefixCut := [⟨64,172363939,172364045⟩]
theorem checked71235 : checkPrefixCuts (2^48) 9340846081 10 Manual.Count131072.C071235.packed 64 cuts71235 = true := by
 decide +kernel
def cuts71236 : List PrefixCut := [⟨7,18652528,18652538⟩,
⟨64,169890611,169890712⟩]
theorem checked71236 : checkPrefixCuts (2^48) 9340977153 10 Manual.Count131072.C071236.packed 64 cuts71236 = true := by
 decide +kernel
def pointBounds71236 : List (Nat × Nat × Nat) := [(9340991488,116028380278398,116028769910256)]
theorem point_links_checked71236 : (cuts71236.take 1).map (fun c => (9340977153-1+2*2^10*c.k,116028361625870+c.lower,116028751257718+c.upper)) = pointBounds71236 := by
 decide +kernel
def cuts71237 : List PrefixCut := [⟨64,172991892,172991999⟩]
theorem checked71237 : checkPrefixCuts (2^48) 9341108225 10 Manual.Count131072.C071237.packed 64 cuts71237 = true := by
 decide +kernel
def cuts71238 : List PrefixCut := [⟨22,58667838,58667871⟩,
⟨64,169915970,169916073⟩]
theorem checked71238 : checkPrefixCuts (2^48) 9341239297 10 Manual.Count131072.C071238.packed 64 cuts71238 = true := by
 decide +kernel
def pointBounds71238 : List (Nat × Nat × Nat) := [(9341284352,116028763176211,116029152808300)]
theorem point_links_checked71238 : (cuts71238.take 1).map (fun c => (9341239297-1+2*2^10*c.k,116028704508373+c.lower,116029094140429+c.upper)) = pointBounds71238 := by
 decide +kernel
def cuts71239 : List PrefixCut := [⟨64,171842033,171842133⟩]
theorem checked71239 : checkPrefixCuts (2^48) 9341370369 10 Manual.Count131072.C071239.packed 64 cuts71239 = true := by
 decide +kernel
def cuts71240 : List PrefixCut := [⟨37,101061164,101061222⟩,
⟨64,173044889,173044987⟩]
theorem checked71240 : checkPrefixCuts (2^48) 9341501441 10 Manual.Count131072.C071240.packed 64 cuts71240 = true := by
 decide +kernel
def pointBounds71240 : List (Nat × Nat × Nat) := [(9341577216,116029147327540,116029536959857)]
theorem point_links_checked71240 : (cuts71240.take 1).map (fun c => (9341501441-1+2*2^10*c.k,116029046266376+c.lower,116029435898635+c.upper)) = pointBounds71240 := by
 decide +kernel
def cuts71241 : List PrefixCut := [⟨64,169818424,169818524⟩]
theorem checked71241 : checkPrefixCuts (2^48) 9341632513 10 Manual.Count131072.C071241.packed 64 cuts71241 = true := by
 decide +kernel
def cuts71242 : List PrefixCut := [⟨52,138811844,138811926⟩,
⟨64,170629574,170629675⟩]
theorem checked71242 : checkPrefixCuts (2^48) 9341763585 10 Manual.Count131072.C071242.packed 64 cuts71242 = true := by
 decide +kernel
def pointBounds71242 : List (Nat × Nat × Nat) := [(9341870080,116029527941533,116029917574072)]
theorem point_links_checked71242 : (cuts71242.take 1).map (fun c => (9341763585-1+2*2^10*c.k,116029389129689+c.lower,116029778762146+c.upper)) = pointBounds71242 := by
 decide +kernel
def cuts71243 : List PrefixCut := [⟨64,170898352,170898452⟩]
theorem checked71243 : checkPrefixCuts (2^48) 9341894657 10 Manual.Count131072.C071243.packed 64 cuts71243 = true := by
 decide +kernel
def cuts71244 : List PrefixCut := [⟨64,170383753,170383851⟩]
theorem checked71244 : checkPrefixCuts (2^48) 9342025729 10 Manual.Count131072.C071244.packed 64 cuts71244 = true := by
 decide +kernel
def cuts71245 : List PrefixCut := [⟨3,7743290,7743294⟩,
⟨64,170622389,170622490⟩]
theorem checked71245 : checkPrefixCuts (2^48) 9342156801 10 Manual.Count131072.C071245.packed 64 cuts71245 = true := by
 decide +kernel
def pointBounds71245 : List (Nat × Nat × Nat) := [(9342162944,116029908784658,116030298417418)]
theorem point_links_checked71245 : (cuts71245.take 1).map (fun c => (9342156801-1+2*2^10*c.k,116029901041368+c.lower,116030290674124+c.upper)) = pointBounds71245 := by
 decide +kernel
def cuts71246 : List PrefixCut := [⟨64,171584113,171584215⟩]
theorem checked71246 : checkPrefixCuts (2^48) 9342287873 10 Manual.Count131072.C071246.packed 64 cuts71246 = true := by
 decide +kernel
def cuts71247 : List PrefixCut := [⟨18,48507106,48507132⟩,
⟨64,172786856,172786954⟩]
theorem checked71247 : checkPrefixCuts (2^48) 9342418945 10 Manual.Count131072.C071247.packed 64 cuts71247 = true := by
 decide +kernel
def pointBounds71247 : List (Nat × Nat × Nat) := [(9342455808,116030291754976,116030681387961)]
theorem point_links_checked71247 : (cuts71247.take 1).map (fun c => (9342418945-1+2*2^10*c.k,116030243247870+c.lower,116030632880829+c.upper)) = pointBounds71247 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000038
