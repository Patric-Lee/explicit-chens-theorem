import PlattAssemblyKernel
import PlattCertificates.Count131072.C070224
import PlattCertificates.Count131072.C070225
import PlattCertificates.Count131072.C070226
import PlattCertificates.Count131072.C070227
import PlattCertificates.Count131072.C070228
import PlattCertificates.Count131072.C070229
import PlattCertificates.Count131072.C070230
import PlattCertificates.Count131072.C070231
import PlattCertificates.Count131072.C070232
import PlattCertificates.Count131072.C070233
import PlattCertificates.Count131072.C070234
import PlattCertificates.Count131072.C070235
import PlattCertificates.Count131072.C070236
import PlattCertificates.Count131072.C070237
import PlattCertificates.Count131072.C070238
import PlattCertificates.Count131072.C070239
import PlattCertificates.Count131072.C070240
import PlattCertificates.Count131072.C070241
import PlattCertificates.Count131072.C070242
import PlattCertificates.Count131072.C070243
import PlattCertificates.Count131072.C070244
import PlattCertificates.Count131072.C070245
import PlattCertificates.Count131072.C070246
import PlattCertificates.Count131072.C070247
import PlattCertificates.Count131072.C070248
import PlattCertificates.Count131072.C070249
import PlattCertificates.Count131072.C070250
import PlattCertificates.Count131072.C070251
import PlattCertificates.Count131072.C070252
import PlattCertificates.Count131072.C070253
import PlattCertificates.Count131072.C070254
import PlattCertificates.Count131072.C070255
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70224 : List PrefixCut := [⟨17,46187272,46187300⟩,
⟨64,174019030,174019141⟩]
theorem checked70224 : checkPrefixCuts (2^48) 9208332289 10 Manual.Count131072.C070224.packed 64 cuts70224 = true := by
 decide +kernel
def pointBounds70224 : List (Nat × Nat × Nat) := [(9208367104,115852947233863,115853336762110)]
theorem point_links_checked70224 : (cuts70224.take 1).map (fun c => (9208332289-1+2*2^10*c.k,115852901046591+c.lower,115853290574810+c.upper)) = pointBounds70224 := by
 decide +kernel
def cuts70225 : List PrefixCut := [⟨64,176736999,176737099⟩]
theorem checked70225 : checkPrefixCuts (2^48) 9208463361 10 Manual.Count131072.C070225.packed 64 cuts70225 = true := by
 decide +kernel
def cuts70226 : List PrefixCut := [⟨30,82223723,82223773⟩,
⟨64,172852576,172852678⟩]
theorem checked70226 : checkPrefixCuts (2^48) 9208594433 10 Manual.Count131072.C070226.packed 64 cuts70226 = true := by
 decide +kernel
def pointBounds70226 : List (Nat × Nat × Nat) := [(9208655872,115853334026343,115853723554823)]
theorem point_links_checked70226 : (cuts70226.take 1).map (fun c => (9208594433-1+2*2^10*c.k,115853251802620+c.lower,115853641331050+c.upper)) = pointBounds70226 := by
 decide +kernel
def cuts70227 : List PrefixCut := [⟨64,173553125,173553220⟩]
theorem checked70227 : checkPrefixCuts (2^48) 9208725505 10 Manual.Count131072.C070227.packed 64 cuts70227 = true := by
 decide +kernel
def cuts70228 : List PrefixCut := [⟨43,116852006,116852077⟩,
⟨64,174926093,174926200⟩]
theorem checked70228 : checkPrefixCuts (2^48) 9208856577 10 Manual.Count131072.C070228.packed 64 cuts70228 = true := by
 decide +kernel
def pointBounds70228 : List (Nat × Nat × Nat) := [(9208944640,115853715060327,115854104589025)]
theorem point_links_checked70228 : (cuts70228.take 1).map (fun c => (9208856577-1+2*2^10*c.k,115853598208321+c.lower,115853987736948+c.upper)) = pointBounds70228 := by
 decide +kernel
def cuts70229 : List PrefixCut := [⟨64,174923617,174923722⟩]
theorem checked70229 : checkPrefixCuts (2^48) 9208987649 10 Manual.Count131072.C070229.packed 64 cuts70229 = true := by
 decide +kernel
def cuts70230 : List PrefixCut := [⟨56,151141997,151142085⟩,
⟨64,172537074,172537172⟩]
theorem checked70230 : checkPrefixCuts (2^48) 9209118721 10 Manual.Count131072.C070230.packed 64 cuts70230 = true := by
 decide +kernel
def pointBounds70230 : List (Nat × Nat × Nat) := [(9209233408,115854099200028,115854488728955)]
theorem point_links_checked70230 : (cuts70230.take 1).map (fun c => (9209118721-1+2*2^10*c.k,115853948058031+c.lower,115854337586870+c.upper)) = pointBounds70230 := by
 decide +kernel
def cuts70231 : List PrefixCut := [⟨64,176171762,176171860⟩]
theorem checked70231 : checkPrefixCuts (2^48) 9209249793 10 Manual.Count131072.C070231.packed 64 cuts70231 = true := by
 decide +kernel
def cuts70232 : List PrefixCut := [⟨64,174304864,174304964⟩]
theorem checked70232 : checkPrefixCuts (2^48) 9209380865 10 Manual.Count131072.C070232.packed 64 cuts70232 = true := by
 decide +kernel
def cuts70233 : List PrefixCut := [⟨5,14548216,14548224⟩,
⟨64,175463793,175463884⟩]
theorem checked70233 : checkPrefixCuts (2^48) 9209511937 10 Manual.Count131072.C070233.packed 64 cuts70233 = true := by
 decide +kernel
def pointBounds70233 : List (Nat × Nat × Nat) := [(9209522176,115854485619947,115854875149090)]
theorem point_links_checked70233 : (cuts70233.take 1).map (fun c => (9209511937-1+2*2^10*c.k,115854471071731+c.lower,115854860600866+c.upper)) = pointBounds70233 := by
 decide +kernel
def cuts70234 : List PrefixCut := [⟨64,176408752,176408860⟩]
theorem checked70234 : checkPrefixCuts (2^48) 9209643009 10 Manual.Count131072.C070234.packed 64 cuts70234 = true := by
 decide +kernel
def cuts70235 : List PrefixCut := [⟨18,48961231,48961261⟩,
⟨64,176528475,176528576⟩]
theorem checked70235 : checkPrefixCuts (2^48) 9209774081 10 Manual.Count131072.C070235.packed 64 cuts70235 = true := by
 decide +kernel
def pointBounds70235 : List (Nat × Nat × Nat) := [(9209810944,115854871905507,115855261434871)]
theorem point_links_checked70235 : (cuts70235.take 1).map (fun c => (9209774081-1+2*2^10*c.k,115854822944276+c.lower,115855212473610+c.upper)) = pointBounds70235 := by
 decide +kernel
def cuts70236 : List PrefixCut := [⟨64,177259456,177259562⟩]
theorem checked70236 : checkPrefixCuts (2^48) 9209905153 10 Manual.Count131072.C070236.packed 64 cuts70236 = true := by
 decide +kernel
def cuts70237 : List PrefixCut := [⟨31,84258478,84258527⟩,
⟨64,174720321,174720426⟩]
theorem checked70237 : checkPrefixCuts (2^48) 9210036225 10 Manual.Count131072.C070237.packed 64 cuts70237 = true := by
 decide +kernel
def pointBounds70237 : List (Nat × Nat × Nat) := [(9210099712,115855260990685,115855650520275)]
theorem point_links_checked70237 : (cuts70237.take 1).map (fun c => (9210036225-1+2*2^10*c.k,115855176732207+c.lower,115855566261748+c.upper)) = pointBounds70237 := by
 decide +kernel
def cuts70238 : List PrefixCut := [⟨64,174748391,174748498⟩]
theorem checked70238 : checkPrefixCuts (2^48) 9210167297 10 Manual.Count131072.C070238.packed 64 cuts70238 = true := by
 decide +kernel
def cuts70239 : List PrefixCut := [⟨44,116864262,116864333⟩,
⟨64,171567594,171567698⟩]
theorem checked70239 : checkPrefixCuts (2^48) 9210298369 10 Manual.Count131072.C070239.packed 64 cuts70239 = true := by
 decide +kernel
def pointBounds70239 : List (Nat × Nat × Nat) := [(9210388480,115855643065181,115856032595005)]
theorem point_links_checked70239 : (cuts70239.take 1).map (fun c => (9210298369-1+2*2^10*c.k,115855526200919+c.lower,115855915730672+c.upper)) = pointBounds70239 := by
 decide +kernel
def cuts70240 : List PrefixCut := [⟨64,174346145,174346247⟩]
theorem checked70240 : checkPrefixCuts (2^48) 9210429441 10 Manual.Count131072.C070240.packed 64 cuts70240 = true := by
 decide +kernel
def cuts70241 : List PrefixCut := [⟨57,156038446,156038540⟩,
⟨64,174465889,174465994⟩]
theorem checked70241 : checkPrefixCuts (2^48) 9210560513 10 Manual.Count131072.C070241.packed 64 cuts70241 = true := by
 decide +kernel
def pointBounds70241 : List (Nat × Nat × Nat) := [(9210677248,115856028153104,115856417683157)]
theorem point_links_checked70241 : (cuts70241.take 1).map (fun c => (9210560513-1+2*2^10*c.k,115855872114658+c.lower,115856261644617+c.upper)) = pointBounds70241 := by
 decide +kernel
def cuts70242 : List PrefixCut := [⟨64,171926996,171927090⟩]
theorem checked70242 : checkPrefixCuts (2^48) 9210691585 10 Manual.Count131072.C070242.packed 64 cuts70242 = true := by
 decide +kernel
def cuts70243 : List PrefixCut := [⟨64,173391364,173391465⟩]
theorem checked70243 : checkPrefixCuts (2^48) 9210822657 10 Manual.Count131072.C070243.packed 64 cuts70243 = true := by
 decide +kernel
def cuts70244 : List PrefixCut := [⟨6,16715605,16715616⟩,
⟨64,175955813,175955920⟩]
theorem checked70244 : checkPrefixCuts (2^48) 9210953729 10 Manual.Count131072.C070244.packed 64 cuts70244 = true := by
 decide +kernel
def pointBounds70244 : List (Nat × Nat × Nat) := [(9210966016,115856408614512,115856798144782)]
theorem point_links_checked70244 : (cuts70244.take 1).map (fun c => (9210953729-1+2*2^10*c.k,115856391898907+c.lower,115856781429166+c.upper)) = pointBounds70244 := by
 decide +kernel
def cuts70245 : List PrefixCut := [⟨64,174364297,174364395⟩]
theorem checked70245 : checkPrefixCuts (2^48) 9211084801 10 Manual.Count131072.C070245.packed 64 cuts70245 = true := by
 decide +kernel
def cuts70246 : List PrefixCut := [⟨19,50145315,50145345⟩,
⟨64,174789612,174789716⟩]
theorem checked70246 : checkPrefixCuts (2^48) 9211215873 10 Manual.Count131072.C070246.packed 64 cuts70246 = true := by
 decide +kernel
def pointBounds70246 : List (Nat × Nat × Nat) := [(9211254784,115856792364332,115857181894826)]
theorem point_links_checked70246 : (cuts70246.take 1).map (fun c => (9211215873-1+2*2^10*c.k,115856742219017+c.lower,115857131749481+c.upper)) = pointBounds70246 := by
 decide +kernel
def cuts70247 : List PrefixCut := [⟨64,174512110,174512210⟩]
theorem checked70247 : checkPrefixCuts (2^48) 9211346945 10 Manual.Count131072.C070247.packed 64 cuts70247 = true := by
 decide +kernel
def cuts70248 : List PrefixCut := [⟨32,88401013,88401062⟩,
⟨64,174417980,174418081⟩]
theorem checked70248 : checkPrefixCuts (2^48) 9211478017 10 Manual.Count131072.C070248.packed 64 cuts70248 = true := by
 decide +kernel
def pointBounds70248 : List (Nat × Nat × Nat) := [(9211543552,115857179921752,115857569452469)]
theorem point_links_checked70248 : (cuts70248.take 1).map (fun c => (9211478017-1+2*2^10*c.k,115857091520739+c.lower,115857481051407+c.upper)) = pointBounds70248 := by
 decide +kernel
def cuts70249 : List PrefixCut := [⟨64,176004408,176004516⟩]
theorem checked70249 : checkPrefixCuts (2^48) 9211609089 10 Manual.Count131072.C070249.packed 64 cuts70249 = true := by
 decide +kernel
def cuts70250 : List PrefixCut := [⟨45,121551572,121551648⟩,
⟨64,173710207,173710317⟩]
theorem checked70250 : checkPrefixCuts (2^48) 9211740161 10 Manual.Count131072.C070250.packed 64 cuts70250 = true := by
 decide +kernel
def pointBounds70250 : List (Nat × Nat × Nat) := [(9211832320,115857563494699,115857953025652)]
theorem point_links_checked70250 : (cuts70250.take 1).map (fun c => (9211740161-1+2*2^10*c.k,115857441943127+c.lower,115857831474004+c.upper)) = pointBounds70250 := by
 decide +kernel
def cuts70251 : List PrefixCut := [⟨64,177007726,177007828⟩]
theorem checked70251 : checkPrefixCuts (2^48) 9211871233 10 Manual.Count131072.C070251.packed 64 cuts70251 = true := by
 decide +kernel
def cuts70252 : List PrefixCut := [⟨58,157052888,157052982⟩,
⟨64,173002504,173002608⟩]
theorem checked70252 : checkPrefixCuts (2^48) 9212002305 10 Manual.Count131072.C070252.packed 64 cuts70252 = true := by
 decide +kernel
def pointBounds70252 : List (Nat × Nat × Nat) := [(9212121088,115857949713948,115858339245131)]
theorem point_links_checked70252 : (cuts70252.take 1).map (fun c => (9212002305-1+2*2^10*c.k,115857792661060+c.lower,115858182192149+c.upper)) = pointBounds70252 := by
 decide +kernel
def cuts70253 : List PrefixCut := [⟨64,174619431,174619540⟩]
theorem checked70253 : checkPrefixCuts (2^48) 9212133377 10 Manual.Count131072.C070253.packed 64 cuts70253 = true := by
 decide +kernel
def cuts70254 : List PrefixCut := [⟨64,175197480,175197583⟩]
theorem checked70254 : checkPrefixCuts (2^48) 9212264449 10 Manual.Count131072.C070254.packed 64 cuts70254 = true := by
 decide +kernel
def cuts70255 : List PrefixCut := [⟨7,19982257,19982266⟩,
⟨64,174400593,174400692⟩]
theorem checked70255 : checkPrefixCuts (2^48) 9212395521 10 Manual.Count131072.C070255.packed 64 cuts70255 = true := by
 decide +kernel
def pointBounds70255 : List (Nat × Nat × Nat) := [(9212409856,115858335462732,115858724994146)]
theorem point_links_checked70255 : (cuts70255.take 1).map (fun c => (9212395521-1+2*2^10*c.k,115858315480475+c.lower,115858705011880+c.upper)) = pointBounds70255 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000007
