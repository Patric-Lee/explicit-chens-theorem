import PlattAssemblyKernel
import PlattCertificates.Count131072.C057200
import PlattCertificates.Count131072.C057201
import PlattCertificates.Count131072.C057202
import PlattCertificates.Count131072.C057203
import PlattCertificates.Count131072.C057204
import PlattCertificates.Count131072.C057205
import PlattCertificates.Count131072.C057206
import PlattCertificates.Count131072.C057207
import PlattCertificates.Count131072.C057208
import PlattCertificates.Count131072.C057209
import PlattCertificates.Count131072.C057210
import PlattCertificates.Count131072.C057211
import PlattCertificates.Count131072.C057212
import PlattCertificates.Count131072.C057213
import PlattCertificates.Count131072.C057214
import PlattCertificates.Count131072.C057215
import PlattCertificates.Count131072.C057216
import PlattCertificates.Count131072.C057217
import PlattCertificates.Count131072.C057218
import PlattCertificates.Count131072.C057219
import PlattCertificates.Count131072.C057220
import PlattCertificates.Count131072.C057221
import PlattCertificates.Count131072.C057222
import PlattCertificates.Count131072.C057223
import PlattCertificates.Count131072.C057224
import PlattCertificates.Count131072.C057225
import PlattCertificates.Count131072.C057226
import PlattCertificates.Count131072.C057227
import PlattCertificates.Count131072.C057228
import PlattCertificates.Count131072.C057229
import PlattCertificates.Count131072.C057230
import PlattCertificates.Count131072.C057231
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000225
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57200 : List PrefixCut := [⟨64,212607584,212607708⟩]
theorem checked57200 : checkPrefixCuts (2^48) 7501250561 10 Manual.Count131072.C057200.packed 64 cuts57200 = true := by
 decide +kernel
def cuts57201 : List PrefixCut := [⟨22,75421151,75421193⟩,
⟨64,218757615,218757739⟩]
theorem checked57201 : checkPrefixCuts (2^48) 7501381633 10 Manual.Count131072.C057201.packed 64 cuts57201 = true := by
 decide +kernel
def pointBounds57201 : List (Nat × Nat × Nat) := [(7501426688,113326469383394,113326857454010)]
theorem point_links_checked57201 : (cuts57201.take 1).map (fun c => (7501381633-1+2*2^10*c.k,113326393962243+c.lower,113326782032817+c.upper)) = pointBounds57201 := by
 decide +kernel
def cuts57202 : List PrefixCut := [⟨64,217740678,217740804⟩]
theorem checked57202 : checkPrefixCuts (2^48) 7501512705 10 Manual.Count131072.C057202.packed 64 cuts57202 = true := by
 decide +kernel
def cuts57203 : List PrefixCut := [⟨9,30730286,30730304⟩,
⟨64,215973376,215973501⟩]
theorem checked57203 : checkPrefixCuts (2^48) 7501643777 10 Manual.Count131072.C057203.packed 64 cuts57203 = true := by
 decide +kernel
def pointBounds57203 : List (Nat × Nat × Nat) := [(7501662208,113326861190822,113327249261664)]
theorem point_links_checked57203 : (cuts57203.take 1).map (fun c => (7501643777-1+2*2^10*c.k,113326830460536+c.lower,113327218531360+c.upper)) = pointBounds57203 := by
 decide +kernel
def cuts57204 : List PrefixCut := [⟨60,204488357,204488472⟩,
⟨64,218033247,218033370⟩]
theorem checked57204 : checkPrefixCuts (2^48) 7501774849 10 Manual.Count131072.C057204.packed 64 cuts57204 = true := by
 decide +kernel
def pointBounds57204 : List (Nat × Nat × Nat) := [(7501897728,113327250922269,113327638993333)]
theorem point_links_checked57204 : (cuts57204.take 1).map (fun c => (7501774849-1+2*2^10*c.k,113327046433912+c.lower,113327434504861+c.upper)) = pointBounds57204 := by
 decide +kernel
def cuts57205 : List PrefixCut := [⟨64,215515593,215515716⟩]
theorem checked57205 : checkPrefixCuts (2^48) 7501905921 10 Manual.Count131072.C057205.packed 64 cuts57205 = true := by
 decide +kernel
def cuts57206 : List PrefixCut := [⟨47,155556079,155556169⟩,
⟨64,212022518,212022640⟩]
theorem checked57206 : checkPrefixCuts (2^48) 7502036993 10 Manual.Count131072.C057206.packed 64 cuts57206 = true := by
 decide +kernel
def pointBounds57206 : List (Nat × Nat × Nat) := [(7502133248,113327635538831,113328023610116)]
theorem point_links_checked57206 : (cuts57206.take 1).map (fun c => (7502036993-1+2*2^10*c.k,113327479982752+c.lower,113327868053947+c.upper)) = pointBounds57206 := by
 decide +kernel
def cuts57207 : List PrefixCut := [⟨64,213894768,213894889⟩]
theorem checked57207 : checkPrefixCuts (2^48) 7502168065 10 Manual.Count131072.C057207.packed 64 cuts57207 = true := by
 decide +kernel
def cuts57208 : List PrefixCut := [⟨34,115706475,115706541⟩,
⟨64,219481221,219481342⟩]
theorem checked57208 : checkPrefixCuts (2^48) 7502299137 10 Manual.Count131072.C057208.packed 64 cuts57208 = true := by
 decide +kernel
def pointBounds57208 : List (Nat × Nat × Nat) := [(7502368768,113328021606513,113328409678017)]
theorem point_links_checked57208 : (cuts57208.take 1).map (fun c => (7502299137-1+2*2^10*c.k,113327905900038+c.lower,113328293971476+c.upper)) = pointBounds57208 := by
 decide +kernel
def cuts57209 : List PrefixCut := [⟨64,214825201,214825323⟩]
theorem checked57209 : checkPrefixCuts (2^48) 7502430209 10 Manual.Count131072.C057209.packed 64 cuts57209 = true := by
 decide +kernel
def cuts57210 : List PrefixCut := [⟨21,71019809,71019850⟩,
⟨64,215384215,215384339⟩]
theorem checked57210 : checkPrefixCuts (2^48) 7502561281 10 Manual.Count131072.C057210.packed 64 cuts57210 = true := by
 decide +kernel
def pointBounds57210 : List (Nat × Nat × Nat) := [(7502604288,113328411226269,113328799297991)]
theorem point_links_checked57210 : (cuts57210.take 1).map (fun c => (7502561281-1+2*2^10*c.k,113328340206460+c.lower,113328728278141+c.upper)) = pointBounds57210 := by
 decide +kernel
def cuts57211 : List PrefixCut := [⟨64,215680591,215680717⟩]
theorem checked57211 : checkPrefixCuts (2^48) 7502692353 10 Manual.Count131072.C057211.packed 64 cuts57211 = true := by
 decide +kernel
def cuts57212 : List PrefixCut := [⟨8,27986804,27986820⟩,
⟨64,220703891,220704017⟩]
theorem checked57212 : checkPrefixCuts (2^48) 7502823425 10 Manual.Count131072.C057212.packed 64 cuts57212 = true := by
 decide +kernel
def pointBounds57212 : List (Nat × Nat × Nat) := [(7502839808,113328799258070,113329187330017)]
theorem point_links_checked57212 : (cuts57212.take 1).map (fun c => (7502823425-1+2*2^10*c.k,113328771271266+c.lower,113329159343197+c.upper)) = pointBounds57212 := by
 decide +kernel
def cuts57213 : List PrefixCut := [⟨59,198491360,198491472⟩,
⟨64,215673037,215673159⟩]
theorem checked57213 : checkPrefixCuts (2^48) 7502954497 10 Manual.Count131072.C057213.packed 64 cuts57213 = true := by
 decide +kernel
def pointBounds57213 : List (Nat × Nat × Nat) := [(7503075328,113329190466517,113329578538686)]
theorem point_links_checked57213 : (cuts57213.take 1).map (fun c => (7502954497-1+2*2^10*c.k,113328991975157+c.lower,113329380047214+c.upper)) = pointBounds57213 := by
 decide +kernel
def cuts57214 : List PrefixCut := [⟨64,215256623,215256748⟩]
theorem checked57214 : checkPrefixCuts (2^48) 7503085569 10 Manual.Count131072.C057214.packed 64 cuts57214 = true := by
 decide +kernel
def cuts57215 : List PrefixCut := [⟨46,155794233,155794319⟩,
⟨64,215815567,215815689⟩]
theorem checked57215 : checkPrefixCuts (2^48) 7503216641 10 Manual.Count131072.C057215.packed 64 cuts57215 = true := by
 decide +kernel
def pointBounds57215 : List (Nat × Nat × Nat) := [(7503310848,113329578699050,113329966771440)]
theorem point_links_checked57215 : (cuts57215.take 1).map (fun c => (7503216641-1+2*2^10*c.k,113329422904817+c.lower,113329810977121+c.upper)) = pointBounds57215 := by
 decide +kernel
def cuts57216 : List PrefixCut := [⟨64,213898622,213898745⟩]
theorem checked57216 : checkPrefixCuts (2^48) 7503347713 10 Manual.Count131072.C057216.packed 64 cuts57216 = true := by
 decide +kernel
def cuts57217 : List PrefixCut := [⟨33,111899542,111899608⟩,
⟨64,215170325,215170447⟩]
theorem checked57217 : checkPrefixCuts (2^48) 7503478785 10 Manual.Count131072.C057217.packed 64 cuts57217 = true := by
 decide +kernel
def pointBounds57217 : List (Nat × Nat × Nat) := [(7503546368,113329964518548,113330352591163)]
theorem point_links_checked57217 : (cuts57217.take 1).map (fun c => (7503478785-1+2*2^10*c.k,113329852619006+c.lower,113330240691555+c.upper)) = pointBounds57217 := by
 decide +kernel
def cuts57218 : List PrefixCut := [⟨64,218129965,218130086⟩]
theorem checked57218 : checkPrefixCuts (2^48) 7503609857 10 Manual.Count131072.C057218.packed 64 cuts57218 = true := by
 decide +kernel
def cuts57219 : List PrefixCut := [⟨20,66132198,66132236⟩,
⟨64,215950514,215950634⟩]
theorem checked57219 : checkPrefixCuts (2^48) 7503740929 10 Manual.Count131072.C057219.packed 64 cuts57219 = true := by
 decide +kernel
def pointBounds57219 : List (Nat × Nat × Nat) := [(7503781888,113330352051494,113330740124324)]
theorem point_links_checked57219 : (cuts57219.take 1).map (fun c => (7503740929-1+2*2^10*c.k,113330285919296+c.lower,113330673992088+c.upper)) = pointBounds57219 := by
 decide +kernel
def cuts57220 : List PrefixCut := [⟨64,217072053,217072178⟩]
theorem checked57220 : checkPrefixCuts (2^48) 7503872001 10 Manual.Count131072.C057220.packed 64 cuts57220 = true := by
 decide +kernel
def cuts57221 : List PrefixCut := [⟨7,23968844,23968857⟩,
⟨64,218418622,218418745⟩]
theorem checked57221 : checkPrefixCuts (2^48) 7504003073 10 Manual.Count131072.C057221.packed 64 cuts57221 = true := by
 decide +kernel
def pointBounds57221 : List (Nat × Nat × Nat) := [(7504017408,113330742910707,113331130983757)]
theorem point_links_checked57221 : (cuts57221.take 1).map (fun c => (7504003073-1+2*2^10*c.k,113330718941863+c.lower,113331107014900+c.upper)) = pointBounds57221 := by
 decide +kernel
def cuts57222 : List PrefixCut := [⟨58,196997329,196997442⟩,
⟨64,217627107,217627232⟩]
theorem checked57222 : checkPrefixCuts (2^48) 7504134145 10 Manual.Count131072.C057222.packed 64 cuts57222 = true := by
 decide +kernel
def pointBounds57222 : List (Nat × Nat × Nat) := [(7504252928,113331134357814,113331522431087)]
theorem point_links_checked57222 : (cuts57222.take 1).map (fun c => (7504134145-1+2*2^10*c.k,113330937360485+c.lower,113331325433645+c.upper)) = pointBounds57222 := by
 decide +kernel
def cuts57223 : List PrefixCut := [⟨64,218298465,218298590⟩]
theorem checked57223 : checkPrefixCuts (2^48) 7504265217 10 Manual.Count131072.C057223.packed 64 cuts57223 = true := by
 decide +kernel
def cuts57224 : List PrefixCut := [⟨45,152356563,152356651⟩,
⟨64,215481589,215481712⟩]
theorem checked57224 : checkPrefixCuts (2^48) 7504396289 10 Manual.Count131072.C057224.packed 64 cuts57224 = true := by
 decide +kernel
def pointBounds57224 : List (Nat × Nat × Nat) := [(7504488448,113331525642620,113331913716118)]
theorem point_links_checked57224 : (cuts57224.take 1).map (fun c => (7504396289-1+2*2^10*c.k,113331373286057+c.lower,113331761359467+c.upper)) = pointBounds57224 := by
 decide +kernel
def cuts57225 : List PrefixCut := [⟨64,215665370,215665491⟩]
theorem checked57225 : checkPrefixCuts (2^48) 7504527361 10 Manual.Count131072.C057225.packed 64 cuts57225 = true := by
 decide +kernel
def cuts57226 : List PrefixCut := [⟨32,108018797,108018859⟩,
⟨64,217574403,217574527⟩]
theorem checked57226 : checkPrefixCuts (2^48) 7504658433 10 Manual.Count131072.C057226.packed 64 cuts57226 = true := by
 decide +kernel
def pointBounds57226 : List (Nat × Nat × Nat) := [(7504723968,113331912451813,113332300525529)]
theorem point_links_checked57226 : (cuts57226.take 1).map (fun c => (7504658433-1+2*2^10*c.k,113331804433016+c.lower,113332192506670+c.upper)) = pointBounds57226 := by
 decide +kernel
def cuts57227 : List PrefixCut := [⟨64,218395744,218395867⟩]
theorem checked57227 : checkPrefixCuts (2^48) 7504789505 10 Manual.Count131072.C057227.packed 64 cuts57227 = true := by
 decide +kernel
def cuts57228 : List PrefixCut := [⟨19,64696615,64696650⟩,
⟨64,216704196,216704320⟩]
theorem checked57228 : checkPrefixCuts (2^48) 7504920577 10 Manual.Count131072.C057228.packed 64 cuts57228 = true := by
 decide +kernel
def pointBounds57228 : List (Nat × Nat × Nat) := [(7504959488,113332305099778,113332693173714)]
theorem point_links_checked57228 : (cuts57228.take 1).map (fun c => (7504920577-1+2*2^10*c.k,113332240403163+c.lower,113332628477064+c.upper)) = pointBounds57228 := by
 decide +kernel
def cuts57229 : List PrefixCut := [⟨64,216100356,216100477⟩]
theorem checked57229 : checkPrefixCuts (2^48) 7505051649 10 Manual.Count131072.C057229.packed 64 cuts57229 = true := by
 decide +kernel
def cuts57230 : List PrefixCut := [⟨6,20477205,20477217⟩,
⟨64,217634214,217634338⟩]
theorem checked57230 : checkPrefixCuts (2^48) 7505182721 10 Manual.Count131072.C057230.packed 64 cuts57230 = true := by
 decide +kernel
def pointBounds57230 : List (Nat × Nat × Nat) := [(7505195008,113332693684920,113333081759078)]
theorem point_links_checked57230 : (cuts57230.take 1).map (fun c => (7505182721-1+2*2^10*c.k,113332673207715+c.lower,113333061281861+c.upper)) = pointBounds57230 := by
 decide +kernel
def cuts57231 : List PrefixCut := [⟨57,192766034,192766142⟩,
⟨64,217105348,217105471⟩]
theorem checked57231 : checkPrefixCuts (2^48) 7505313793 10 Manual.Count131072.C057231.packed 64 cuts57231 = true := by
 decide +kernel
def pointBounds57231 : List (Nat × Nat × Nat) := [(7505430528,113333083607963,113333471682341)]
theorem point_links_checked57231 : (cuts57231.take 1).map (fun c => (7505313793-1+2*2^10*c.k,113332890841929+c.lower,113333278916199+c.upper)) = pointBounds57231 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000225
