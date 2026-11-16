import PlattAssemblyKernel
import PlattCertificates.Count131072.C064192
import PlattCertificates.Count131072.C064193
import PlattCertificates.Count131072.C064194
import PlattCertificates.Count131072.C064195
import PlattCertificates.Count131072.C064196
import PlattCertificates.Count131072.C064197
import PlattCertificates.Count131072.C064198
import PlattCertificates.Count131072.C064199
import PlattCertificates.Count131072.C064200
import PlattCertificates.Count131072.C064201
import PlattCertificates.Count131072.C064202
import PlattCertificates.Count131072.C064203
import PlattCertificates.Count131072.C064204
import PlattCertificates.Count131072.C064205
import PlattCertificates.Count131072.C064206
import PlattCertificates.Count131072.C064207
import PlattCertificates.Count131072.C064208
import PlattCertificates.Count131072.C064209
import PlattCertificates.Count131072.C064210
import PlattCertificates.Count131072.C064211
import PlattCertificates.Count131072.C064212
import PlattCertificates.Count131072.C064213
import PlattCertificates.Count131072.C064214
import PlattCertificates.Count131072.C064215
import PlattCertificates.Count131072.C064216
import PlattCertificates.Count131072.C064217
import PlattCertificates.Count131072.C064218
import PlattCertificates.Count131072.C064219
import PlattCertificates.Count131072.C064220
import PlattCertificates.Count131072.C064221
import PlattCertificates.Count131072.C064222
import PlattCertificates.Count131072.C064223
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000131
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64192 : List PrefixCut := [⟨30,89280285,89280338⟩,
⟨64,192436671,192436782⟩]
theorem checked64192 : checkPrefixCuts (2^48) 8417705985 10 Manual.Count131072.C064192.packed 64 cuts64192 = true := by
 decide +kernel
def pointBounds64192 : List (Nat × Nat × Nat) := [(8417767424,114749563105774,114749951990935)]
theorem point_links_checked64192 : (cuts64192.take 1).map (fun c => (8417705985-1+2*2^10*c.k,114749473825489+c.lower,114749862710597+c.upper)) = pointBounds64192 := by
 decide +kernel
def cuts64193 : List PrefixCut := [⟨64,191731494,191731602⟩]
theorem checked64193 : checkPrefixCuts (2^48) 8417837057 10 Manual.Count131072.C064193.packed 64 cuts64193 = true := by
 decide +kernel
def cuts64194 : List PrefixCut := [⟨31,93624341,93624397⟩,
⟨64,189922923,189923030⟩]
theorem checked64194 : checkPrefixCuts (2^48) 8417968129 10 Manual.Count131072.C064194.packed 64 cuts64194 = true := by
 decide +kernel
def pointBounds64194 : List (Nat × Nat × Nat) := [(8418031616,114749951617995,114750340503378)]
theorem point_links_checked64194 : (cuts64194.take 1).map (fun c => (8417968129-1+2*2^10*c.k,114749857993654+c.lower,114750246878981+c.upper)) = pointBounds64194 := by
 decide +kernel
def cuts64195 : List PrefixCut := [⟨64,192126764,192126874⟩]
theorem checked64195 : checkPrefixCuts (2^48) 8418099201 10 Manual.Count131072.C064195.packed 64 cuts64195 = true := by
 decide +kernel
def cuts64196 : List PrefixCut := [⟨32,94891996,94892045⟩,
⟨64,190752894,190752999⟩]
theorem checked64196 : checkPrefixCuts (2^48) 8418230273 10 Manual.Count131072.C064196.packed 64 cuts64196 = true := by
 decide +kernel
def pointBounds64196 : List (Nat × Nat × Nat) := [(8418295808,114750334935337,114750723820930)]
theorem point_links_checked64196 : (cuts64196.take 1).map (fun c => (8418230273-1+2*2^10*c.k,114750240043341+c.lower,114750628928885+c.upper)) = pointBounds64196 := by
 decide +kernel
def cuts64197 : List PrefixCut := [⟨64,190382130,190382238⟩]
theorem checked64197 : checkPrefixCuts (2^48) 8418361345 10 Manual.Count131072.C064197.packed 64 cuts64197 = true := by
 decide +kernel
def cuts64198 : List PrefixCut := [⟨33,99001553,99001610⟩,
⟨64,192084354,192084464⟩]
theorem checked64198 : checkPrefixCuts (2^48) 8418492417 10 Manual.Count131072.C064198.packed 64 cuts64198 = true := by
 decide +kernel
def pointBounds64198 : List (Nat × Nat × Nat) := [(8418560000,114750720179918,114751109065732)]
theorem point_links_checked64198 : (cuts64198.take 1).map (fun c => (8418492417-1+2*2^10*c.k,114750621178365+c.lower,114751010064122+c.upper)) = pointBounds64198 := by
 decide +kernel
def cuts64199 : List PrefixCut := [⟨64,192114802,192114910⟩]
theorem checked64199 : checkPrefixCuts (2^48) 8418623489 10 Manual.Count131072.C064199.packed 64 cuts64199 = true := by
 decide +kernel
def cuts64200 : List PrefixCut := [⟨34,104281054,104281118⟩,
⟨64,192747071,192747192⟩]
theorem checked64200 : checkPrefixCuts (2^48) 8418754561 10 Manual.Count131072.C064200.packed 64 cuts64200 = true := by
 decide +kernel
def pointBounds64200 : List (Nat × Nat × Nat) := [(8418824192,114751109658575,114751498544614)]
theorem point_links_checked64200 : (cuts64200.take 1).map (fun c => (8418754561-1+2*2^10*c.k,114751005377521+c.lower,114751394263496+c.upper)) = pointBounds64200 := by
 decide +kernel
def cuts64201 : List PrefixCut := [⟨64,191440149,191440257⟩]
theorem checked64201 : checkPrefixCuts (2^48) 8418885633 10 Manual.Count131072.C064201.packed 64 cuts64201 = true := by
 decide +kernel
def cuts64202 : List PrefixCut := [⟨35,102739867,102739929⟩,
⟨64,188996555,188996667⟩]
theorem checked64202 : checkPrefixCuts (2^48) 8419016705 10 Manual.Count131072.C064202.packed 64 cuts64202 = true := by
 decide +kernel
def pointBounds64202 : List (Nat × Nat × Nat) := [(8419088384,114751492304608,114751881190874)]
theorem point_links_checked64202 : (cuts64202.take 1).map (fun c => (8419016705-1+2*2^10*c.k,114751389564741+c.lower,114751778450945+c.upper)) = pointBounds64202 := by
 decide +kernel
def cuts64203 : List PrefixCut := [⟨64,190464643,190464759⟩]
theorem checked64203 : checkPrefixCuts (2^48) 8419147777 10 Manual.Count131072.C064203.packed 64 cuts64203 = true := by
 decide +kernel
def cuts64204 : List PrefixCut := [⟨36,109723955,109724017⟩,
⟨64,193236539,193236649⟩]
theorem checked64204 : checkPrefixCuts (2^48) 8419278849 10 Manual.Count131072.C064204.packed 64 cuts64204 = true := by
 decide +kernel
def pointBounds64204 : List (Nat × Nat × Nat) := [(8419352576,114751878749894,114752267636388)]
theorem point_links_checked64204 : (cuts64204.take 1).map (fun c => (8419278849-1+2*2^10*c.k,114751769025939+c.lower,114752157912371+c.upper)) = pointBounds64204 := by
 decide +kernel
def cuts64205 : List PrefixCut := [⟨64,190726162,190726279⟩]
theorem checked64205 : checkPrefixCuts (2^48) 8419409921 10 Manual.Count131072.C064205.packed 64 cuts64205 = true := by
 decide +kernel
def cuts64206 : List PrefixCut := [⟨37,110990900,110990959⟩,
⟨64,192127292,192127396⟩]
theorem checked64206 : checkPrefixCuts (2^48) 8419540993 10 Manual.Count131072.C064206.packed 64 cuts64206 = true := by
 decide +kernel
def pointBounds64206 : List (Nat × Nat × Nat) := [(8419616768,114752263979540,114752652866258)]
theorem point_links_checked64206 : (cuts64206.take 1).map (fun c => (8419540993-1+2*2^10*c.k,114752152988640+c.lower,114752541875299+c.upper)) = pointBounds64206 := by
 decide +kernel
def cuts64207 : List PrefixCut := [⟨64,191221681,191221790⟩]
theorem checked64207 : checkPrefixCuts (2^48) 8419672065 10 Manual.Count131072.C064207.packed 64 cuts64207 = true := by
 decide +kernel
def cuts64208 : List PrefixCut := [⟨38,113728688,113728752⟩,
⟨64,190850984,190851096⟩]
theorem checked64208 : checkPrefixCuts (2^48) 8419803137 10 Manual.Count131072.C064208.packed 64 cuts64208 = true := by
 decide +kernel
def pointBounds64208 : List (Nat × Nat × Nat) := [(8419880960,114752650066301,114753038953237)]
theorem point_links_checked64208 : (cuts64208.take 1).map (fun c => (8419803137-1+2*2^10*c.k,114752536337613+c.lower,114752925224485+c.upper)) = pointBounds64208 := by
 decide +kernel
def cuts64209 : List PrefixCut := [⟨64,195962690,195962807⟩]
theorem checked64209 : checkPrefixCuts (2^48) 8419934209 10 Manual.Count131072.C064209.packed 64 cuts64209 = true := by
 decide +kernel
def cuts64210 : List PrefixCut := [⟨39,116332580,116332649⟩,
⟨64,192215604,192215718⟩]
theorem checked64210 : checkPrefixCuts (2^48) 8420065281 10 Manual.Count131072.C064210.packed 64 cuts64210 = true := by
 decide +kernel
def pointBounds64210 : List (Nat × Nat × Nat) := [(8420145152,114753039483867,114753428371037)]
theorem point_links_checked64210 : (cuts64210.take 1).map (fun c => (8420065281-1+2*2^10*c.k,114752923151287+c.lower,114753312038388+c.upper)) = pointBounds64210 := by
 decide +kernel
def cuts64211 : List PrefixCut := [⟨64,188100948,188101058⟩]
theorem checked64211 : checkPrefixCuts (2^48) 8420196353 10 Manual.Count131072.C064211.packed 64 cuts64211 = true := by
 decide +kernel
def cuts64212 : List PrefixCut := [⟨40,117732925,117732990⟩,
⟨64,191373927,191374035⟩]
theorem checked64212 : checkPrefixCuts (2^48) 8420327425 10 Manual.Count131072.C064212.packed 64 cuts64212 = true := by
 decide +kernel
def pointBounds64212 : List (Nat × Nat × Nat) := [(8420409344,114753421200764,114753810088154)]
theorem point_links_checked64212 : (cuts64212.take 1).map (fun c => (8420327425-1+2*2^10*c.k,114753303467839+c.lower,114753692355164+c.upper)) = pointBounds64212 := by
 decide +kernel
def cuts64213 : List PrefixCut := [⟨64,191638377,191638486⟩]
theorem checked64213 : checkPrefixCuts (2^48) 8420458497 10 Manual.Count131072.C064213.packed 64 cuts64213 = true := by
 decide +kernel
def cuts64214 : List PrefixCut := [⟨41,123010682,123010755⟩,
⟨64,191367986,191368099⟩]
theorem checked64214 : checkPrefixCuts (2^48) 8420589569 10 Manual.Count131072.C064214.packed 64 cuts64214 = true := by
 decide +kernel
def pointBounds64214 : List (Nat × Nat × Nat) := [(8420673536,114753809490825,114754198378440)]
theorem point_links_checked64214 : (cuts64214.take 1).map (fun c => (8420589569-1+2*2^10*c.k,114753686480143+c.lower,114754075367685+c.upper)) = pointBounds64214 := by
 decide +kernel
def cuts64215 : List PrefixCut := [⟨64,190362206,190362311⟩]
theorem checked64215 : checkPrefixCuts (2^48) 8420720641 10 Manual.Count131072.C064215.packed 64 cuts64215 = true := by
 decide +kernel
def cuts64216 : List PrefixCut := [⟨42,127218478,127218551⟩,
⟨64,193701820,193701927⟩]
theorem checked64216 : checkPrefixCuts (2^48) 8420851713 10 Manual.Count131072.C064216.packed 64 cuts64216 = true := by
 decide +kernel
def pointBounds64216 : List (Nat × Nat × Nat) := [(8420937728,114754195428813,114754584316646)]
theorem point_links_checked64216 : (cuts64216.take 1).map (fun c => (8420851713-1+2*2^10*c.k,114754068210335+c.lower,114754457098095+c.upper)) = pointBounds64216 := by
 decide +kernel
def cuts64217 : List PrefixCut := [⟨64,189620938,189621050⟩]
theorem checked64217 : checkPrefixCuts (2^48) 8420982785 10 Manual.Count131072.C064217.packed 64 cuts64217 = true := by
 decide +kernel
def cuts64218 : List PrefixCut := [⟨43,129587660,129587733⟩,
⟨64,194130302,194130413⟩]
theorem checked64218 : checkPrefixCuts (2^48) 8421113857 10 Manual.Count131072.C064218.packed 64 cuts64218 = true := by
 decide +kernel
def pointBounds64218 : List (Nat × Nat × Nat) := [(8421201920,114754581120753,114754970008805)]
theorem point_links_checked64218 : (cuts64218.take 1).map (fun c => (8421113857-1+2*2^10*c.k,114754451533093+c.lower,114754840421072+c.upper)) = pointBounds64218 := by
 decide +kernel
def cuts64219 : List PrefixCut := [⟨64,191252831,191252938⟩]
theorem checked64219 : checkPrefixCuts (2^48) 8421244929 10 Manual.Count131072.C064219.packed 64 cuts64219 = true := by
 decide +kernel
def cuts64220 : List PrefixCut := [⟨44,130920564,130920636⟩,
⟨64,190180291,190180394⟩]
theorem checked64220 : checkPrefixCuts (2^48) 8421376001 10 Manual.Count131072.C064220.packed 64 cuts64220 = true := by
 decide +kernel
def pointBounds64220 : List (Nat × Nat × Nat) := [(8421466112,114754967836790,114755356725059)]
theorem point_links_checked64220 : (cuts64220.take 1).map (fun c => (8421376001-1+2*2^10*c.k,114754836916226+c.lower,114755225804423+c.upper)) = pointBounds64220 := by
 decide +kernel
def cuts64221 : List PrefixCut := [⟨64,190077052,190077162⟩]
theorem checked64221 : checkPrefixCuts (2^48) 8421507073 10 Manual.Count131072.C064221.packed 64 cuts64221 = true := by
 decide +kernel
def cuts64222 : List PrefixCut := [⟨45,133991357,133991430⟩,
⟨64,191745227,191745330⟩]
theorem checked64222 : checkPrefixCuts (2^48) 8421638145 10 Manual.Count131072.C064222.packed 64 cuts64222 = true := by
 decide +kernel
def pointBounds64222 : List (Nat × Nat × Nat) := [(8421730304,114755351164926,114755740053409)]
theorem point_links_checked64222 : (cuts64222.take 1).map (fun c => (8421638145-1+2*2^10*c.k,114755217173569+c.lower,114755606061979+c.upper)) = pointBounds64222 := by
 decide +kernel
def cuts64223 : List PrefixCut := [⟨64,193112538,193112654⟩]
theorem checked64223 : checkPrefixCuts (2^48) 8421769217 10 Manual.Count131072.C064223.packed 64 cuts64223 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000131
