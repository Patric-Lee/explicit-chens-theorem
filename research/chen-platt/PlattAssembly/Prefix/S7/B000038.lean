import PlattAssemblyKernel
import PlattCertificates.Count131072.C061216
import PlattCertificates.Count131072.C061217
import PlattCertificates.Count131072.C061218
import PlattCertificates.Count131072.C061219
import PlattCertificates.Count131072.C061220
import PlattCertificates.Count131072.C061221
import PlattCertificates.Count131072.C061222
import PlattCertificates.Count131072.C061223
import PlattCertificates.Count131072.C061224
import PlattCertificates.Count131072.C061225
import PlattCertificates.Count131072.C061226
import PlattCertificates.Count131072.C061227
import PlattCertificates.Count131072.C061228
import PlattCertificates.Count131072.C061229
import PlattCertificates.Count131072.C061230
import PlattCertificates.Count131072.C061231
import PlattCertificates.Count131072.C061232
import PlattCertificates.Count131072.C061233
import PlattCertificates.Count131072.C061234
import PlattCertificates.Count131072.C061235
import PlattCertificates.Count131072.C061236
import PlattCertificates.Count131072.C061237
import PlattCertificates.Count131072.C061238
import PlattCertificates.Count131072.C061239
import PlattCertificates.Count131072.C061240
import PlattCertificates.Count131072.C061241
import PlattCertificates.Count131072.C061242
import PlattCertificates.Count131072.C061243
import PlattCertificates.Count131072.C061244
import PlattCertificates.Count131072.C061245
import PlattCertificates.Count131072.C061246
import PlattCertificates.Count131072.C061247
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000038
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61216 : List PrefixCut := [⟨64,200104253,200104368⟩]
theorem checked61216 : checkPrefixCuts (2^48) 8027635713 10 Manual.Count131072.C061216.packed 64 cuts61216 = true := by
 decide +kernel
def cuts61217 : List PrefixCut := [⟨4,13253680,13253688⟩,
⟨64,201713880,201713997⟩]
theorem checked61217 : checkPrefixCuts (2^48) 8027766785 10 Manual.Count131072.C061217.packed 64 cuts61217 = true := by
 decide +kernel
def pointBounds61217 : List (Nat × Nat × Nat) := [(8027774976,114164670398955,114165058947876)]
theorem point_links_checked61217 : (cuts61217.take 1).map (fun c => (8027766785-1+2*2^10*c.k,114164657145275+c.lower,114165045694188+c.upper)) = pointBounds61217 := by
 decide +kernel
def cuts61218 : List PrefixCut := [⟨63,198379725,198379840⟩,
⟨64,201430078,201430194⟩]
theorem checked61218 : checkPrefixCuts (2^48) 8027897857 10 Manual.Count131072.C061218.packed 64 cuts61218 = true := by
 decide +kernel
def pointBounds61218 : List (Nat × Nat × Nat) := [(8028026880,114165057238880,114165445788025)]
theorem point_links_checked61218 : (cuts61218.take 1).map (fun c => (8027897857-1+2*2^10*c.k,114164858859155+c.lower,114165247408185+c.upper)) = pointBounds61218 := by
 decide +kernel
def cuts61219 : List PrefixCut := [⟨64,201567036,201567150⟩]
theorem checked61219 : checkPrefixCuts (2^48) 8028028929 10 Manual.Count131072.C061219.packed 64 cuts61219 = true := by
 decide +kernel
def cuts61220 : List PrefixCut := [⟨58,180106755,180106860⟩,
⟨64,199950941,199951058⟩]
theorem checked61220 : checkPrefixCuts (2^48) 8028160001 10 Manual.Count131072.C061220.packed 64 cuts61220 = true := by
 decide +kernel
def pointBounds61220 : List (Nat × Nat × Nat) := [(8028278784,114165441963024,114165830512389)]
theorem point_links_checked61220 : (cuts61220.take 1).map (fun c => (8028160001-1+2*2^10*c.k,114165261856269+c.lower,114165650405529+c.upper)) = pointBounds61220 := by
 decide +kernel
def cuts61221 : List PrefixCut := [⟨64,203488768,203488887⟩]
theorem checked61221 : checkPrefixCuts (2^48) 8028291073 10 Manual.Count131072.C061221.packed 64 cuts61221 = true := by
 decide +kernel
def cuts61222 : List PrefixCut := [⟨53,167795074,167795173⟩,
⟨64,201627279,201627398⟩]
theorem checked61222 : checkPrefixCuts (2^48) 8028422145 10 Manual.Count131072.C061222.packed 64 cuts61222 = true := by
 decide +kernel
def pointBounds61222 : List (Nat × Nat × Nat) := [(8028530688,114165833091052,114166221640647)]
theorem point_links_checked61222 : (cuts61222.take 1).map (fun c => (8028422145-1+2*2^10*c.k,114165665295978+c.lower,114166053845474+c.upper)) = pointBounds61222 := by
 decide +kernel
def cuts61223 : List PrefixCut := [⟨64,199730805,199730918⟩]
theorem checked61223 : checkPrefixCuts (2^48) 8028553217 10 Manual.Count131072.C061223.packed 64 cuts61223 = true := by
 decide +kernel
def cuts61224 : List PrefixCut := [⟨48,151662821,151662909⟩,
⟨64,203268428,203268547⟩]
theorem checked61224 : checkPrefixCuts (2^48) 8028684289 10 Manual.Count131072.C061224.packed 64 cuts61224 = true := by
 decide +kernel
def pointBounds61224 : List (Nat × Nat × Nat) := [(8028782592,114166218316883,114166606866699)]
theorem point_links_checked61224 : (cuts61224.take 1).map (fun c => (8028684289-1+2*2^10*c.k,114166066654062+c.lower,114166455203790+c.upper)) = pointBounds61224 := by
 decide +kernel
def cuts61225 : List PrefixCut := [⟨64,198076562,198076679⟩]
theorem checked61225 : checkPrefixCuts (2^48) 8028815361 10 Manual.Count131072.C061225.packed 64 cuts61225 = true := by
 decide +kernel
def cuts61226 : List PrefixCut := [⟨43,135952294,135952368⟩,
⟨64,202946287,202946397⟩]
theorem checked61226 : checkPrefixCuts (2^48) 8028946433 10 Manual.Count131072.C061226.packed 64 cuts61226 = true := by
 decide +kernel
def pointBounds61226 : List (Nat × Nat × Nat) := [(8029034496,114166603951346,114166992501384)]
theorem point_links_checked61226 : (cuts61226.take 1).map (fun c => (8028946433-1+2*2^10*c.k,114166467999052+c.lower,114166856549016+c.upper)) = pointBounds61226 := by
 decide +kernel
def cuts61227 : List PrefixCut := [⟨64,199752833,199752945⟩]
theorem checked61227 : checkPrefixCuts (2^48) 8029077505 10 Manual.Count131072.C061227.packed 64 cuts61227 = true := by
 decide +kernel
def cuts61228 : List PrefixCut := [⟨38,120418049,120418118⟩,
⟨64,202904606,202904724⟩]
theorem checked61228 : checkPrefixCuts (2^48) 8029208577 10 Manual.Count131072.C061228.packed 64 cuts61228 = true := by
 decide +kernel
def pointBounds61228 : List (Nat × Nat × Nat) := [(8029286400,114166991116221,114167379666476)]
theorem point_links_checked61228 : (cuts61228.take 1).map (fun c => (8029208577-1+2*2^10*c.k,114166870698172+c.lower,114167259248358+c.upper)) = pointBounds61228 := by
 decide +kernel
def cuts61229 : List PrefixCut := [⟨64,198729706,198729820⟩]
theorem checked61229 : checkPrefixCuts (2^48) 8029339649 10 Manual.Count131072.C061229.packed 64 cuts61229 = true := by
 decide +kernel
def cuts61230 : List PrefixCut := [⟨33,105340503,105340564⟩,
⟨64,200934909,200935029⟩]
theorem checked61230 : checkPrefixCuts (2^48) 8029470721 10 Manual.Count131072.C061230.packed 64 cuts61230 = true := by
 decide +kernel
def pointBounds61230 : List (Nat × Nat × Nat) := [(8029538304,114167377672987,114167766223466)]
theorem point_links_checked61230 : (cuts61230.take 1).map (fun c => (8029470721-1+2*2^10*c.k,114167272332484+c.lower,114167660882902+c.upper)) = pointBounds61230 := by
 decide +kernel
def cuts61231 : List PrefixCut := [⟨64,202509086,202509201⟩]
theorem checked61231 : checkPrefixCuts (2^48) 8029601793 10 Manual.Count131072.C061231.packed 64 cuts61231 = true := by
 decide +kernel
def cuts61232 : List PrefixCut := [⟨28,90018558,90018608⟩,
⟨64,202085139,202085256⟩]
theorem checked61232 : checkPrefixCuts (2^48) 8029732865 10 Manual.Count131072.C061232.packed 64 cuts61232 = true := by
 decide +kernel
def pointBounds61232 : List (Nat × Nat × Nat) := [(8029790208,114167765795037,114168154345740)]
theorem point_links_checked61232 : (cuts61232.take 1).map (fun c => (8029732865-1+2*2^10*c.k,114167675776479+c.lower,114168064327132+c.upper)) = pointBounds61232 := by
 decide +kernel
def cuts61233 : List PrefixCut := [⟨64,200890008,200890126⟩]
theorem checked61233 : checkPrefixCuts (2^48) 8029863937 10 Manual.Count131072.C061233.packed 64 cuts61233 = true := by
 decide +kernel
def cuts61234 : List PrefixCut := [⟨23,73505794,73505836⟩,
⟨64,201622848,201622963⟩]
theorem checked61234 : checkPrefixCuts (2^48) 8029995009 10 Manual.Count131072.C061234.packed 64 cuts61234 = true := by
 decide +kernel
def pointBounds61234 : List (Nat × Nat × Nat) := [(8030042112,114168152257420,114168540808350)]
theorem point_links_checked61234 : (cuts61234.take 1).map (fun c => (8029995009-1+2*2^10*c.k,114168078751626+c.lower,114168467302514+c.upper)) = pointBounds61234 := by
 decide +kernel
def cuts61235 : List PrefixCut := [⟨64,201759756,201759865⟩]
theorem checked61235 : checkPrefixCuts (2^48) 8030126081 10 Manual.Count131072.C061235.packed 64 cuts61235 = true := by
 decide +kernel
def cuts61236 : List PrefixCut := [⟨18,58150790,58150823⟩,
⟨64,205506983,205507098⟩]
theorem checked61236 : checkPrefixCuts (2^48) 8030257153 10 Manual.Count131072.C061236.packed 64 cuts61236 = true := by
 decide +kernel
def pointBounds61236 : List (Nat × Nat × Nat) := [(8030294016,114168540285020,114168928836165)]
theorem point_links_checked61236 : (cuts61236.take 1).map (fun c => (8030257153-1+2*2^10*c.k,114168482134230+c.lower,114168870685342+c.upper)) = pointBounds61236 := by
 decide +kernel
def cuts61237 : List PrefixCut := [⟨64,199685163,199685275⟩]
theorem checked61237 : checkPrefixCuts (2^48) 8030388225 10 Manual.Count131072.C061237.packed 64 cuts61237 = true := by
 decide +kernel
def cuts61238 : List PrefixCut := [⟨13,41079289,41079314⟩,
⟨64,201083911,201084031⟩]
theorem checked61238 : checkPrefixCuts (2^48) 8030519297 10 Manual.Count131072.C061238.packed 64 cuts61238 = true := by
 decide +kernel
def pointBounds61238 : List (Nat × Nat × Nat) := [(8030545920,114168928405665,114169316957029)]
theorem point_links_checked61238 : (cuts61238.take 1).map (fun c => (8030519297-1+2*2^10*c.k,114168887326376+c.lower,114169275877715+c.upper)) = pointBounds61238 := by
 decide +kernel
def cuts61239 : List PrefixCut := [⟨64,200835291,200835407⟩]
theorem checked61239 : checkPrefixCuts (2^48) 8030650369 10 Manual.Count131072.C061239.packed 64 cuts61239 = true := by
 decide +kernel
def cuts61240 : List PrefixCut := [⟨8,25375814,25375829⟩,
⟨64,201392795,201392912⟩]
theorem checked61240 : checkPrefixCuts (2^48) 8030781441 10 Manual.Count131072.C061240.packed 64 cuts61240 = true := by
 decide +kernel
def pointBounds61240 : List (Nat × Nat × Nat) := [(8030797824,114169314621392,114169703172982)]
theorem point_links_checked61240 : (cuts61240.take 1).map (fun c => (8030781441-1+2*2^10*c.k,114169289245578+c.lower,114169677797153+c.upper)) = pointBounds61240 := by
 decide +kernel
def cuts61241 : List PrefixCut := [⟨64,204403702,204403814⟩]
theorem checked61241 : checkPrefixCuts (2^48) 8030912513 10 Manual.Count131072.C061241.packed 64 cuts61241 = true := by
 decide +kernel
def cuts61242 : List PrefixCut := [⟨3,9813536,9813542⟩,
⟨64,200124484,200124599⟩]
theorem checked61242 : checkPrefixCuts (2^48) 8031043585 10 Manual.Count131072.C061242.packed 64 cuts61242 = true := by
 decide +kernel
def pointBounds61242 : List (Nat × Nat × Nat) := [(8031049728,114169704855611,114170093407421)]
theorem point_links_checked61242 : (cuts61242.take 1).map (fun c => (8031043585-1+2*2^10*c.k,114169695042075+c.lower,114170083593879+c.upper)) = pointBounds61242 := by
 decide +kernel
def cuts61243 : List PrefixCut := [⟨62,194829103,194829214⟩,
⟨64,201347887,201348002⟩]
theorem checked61243 : checkPrefixCuts (2^48) 8031174657 10 Manual.Count131072.C061243.packed 64 cuts61243 = true := by
 decide +kernel
def pointBounds61243 : List (Nat × Nat × Nat) := [(8031301632,114170089995662,114170478547692)]
theorem point_links_checked61243 : (cuts61243.take 1).map (fun c => (8031174657-1+2*2^10*c.k,114169895166559+c.lower,114170283718478+c.upper)) = pointBounds61243 := by
 decide +kernel
def cuts61244 : List PrefixCut := [⟨64,201099276,201099393⟩]
theorem checked61244 : checkPrefixCuts (2^48) 8031305729 10 Manual.Count131072.C061244.packed 64 cuts61244 = true := by
 decide +kernel
def cuts61245 : List PrefixCut := [⟨57,179717879,179717981⟩,
⟨64,202077292,202077407⟩]
theorem checked61245 : checkPrefixCuts (2^48) 8031436801 10 Manual.Count131072.C061245.packed 64 cuts61245 = true := by
 decide +kernel
def pointBounds61245 : List (Nat × Nat × Nat) := [(8031553536,114170477331601,114170865883854)]
theorem point_links_checked61245 : (cuts61245.take 1).map (fun c => (8031436801-1+2*2^10*c.k,114170297613722+c.lower,114170686165873+c.upper)) = pointBounds61245 := by
 decide +kernel
def cuts61246 : List PrefixCut := [⟨64,202529600,202529715⟩]
theorem checked61246 : checkPrefixCuts (2^48) 8031567873 10 Manual.Count131072.C061246.packed 64 cuts61246 = true := by
 decide +kernel
def cuts61247 : List PrefixCut := [⟨52,161348407,161348498⟩,
⟨64,199056806,199056920⟩]
theorem checked61247 : checkPrefixCuts (2^48) 8031698945 10 Manual.Count131072.C061247.packed 64 cuts61247 = true := by
 decide +kernel
def pointBounds61247 : List (Nat × Nat × Nat) := [(8031805440,114170863569021,114171252121493)]
theorem point_links_checked61247 : (cuts61247.take 1).map (fun c => (8031698945-1+2*2^10*c.k,114170702220614+c.lower,114171090772995+c.upper)) = pointBounds61247 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000038
