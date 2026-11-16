import PlattAssemblyKernel
import PlattCertificates.Count131072.C067328
import PlattCertificates.Count131072.C067329
import PlattCertificates.Count131072.C067330
import PlattCertificates.Count131072.C067331
import PlattCertificates.Count131072.C067332
import PlattCertificates.Count131072.C067333
import PlattCertificates.Count131072.C067334
import PlattCertificates.Count131072.C067335
import PlattCertificates.Count131072.C067336
import PlattCertificates.Count131072.C067337
import PlattCertificates.Count131072.C067338
import PlattCertificates.Count131072.C067339
import PlattCertificates.Count131072.C067340
import PlattCertificates.Count131072.C067341
import PlattCertificates.Count131072.C067342
import PlattCertificates.Count131072.C067343
import PlattCertificates.Count131072.C067344
import PlattCertificates.Count131072.C067345
import PlattCertificates.Count131072.C067346
import PlattCertificates.Count131072.C067347
import PlattCertificates.Count131072.C067348
import PlattCertificates.Count131072.C067349
import PlattCertificates.Count131072.C067350
import PlattCertificates.Count131072.C067351
import PlattCertificates.Count131072.C067352
import PlattCertificates.Count131072.C067353
import PlattCertificates.Count131072.C067354
import PlattCertificates.Count131072.C067355
import PlattCertificates.Count131072.C067356
import PlattCertificates.Count131072.C067357
import PlattCertificates.Count131072.C067358
import PlattCertificates.Count131072.C067359
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000229
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67328 : List PrefixCut := [⟨41,118471586,118471653⟩,
⟨64,183318039,183318142⟩]
theorem checked67328 : checkPrefixCuts (2^48) 8828747777 10 Manual.Count131072.C067328.packed 64 cuts67328 = true := by
 decide +kernel
def pointBounds67328 : List (Nat × Nat × Nat) := [(8828831744,115336146307275,115336535532602)]
theorem point_links_checked67328 : (cuts67328.take 1).map (fun c => (8828747777-1+2*2^10*c.k,115336027835689+c.lower,115336417060949+c.upper)) = pointBounds67328 := by
 decide +kernel
def cuts67329 : List PrefixCut := [⟨64,183889157,183889263⟩]
theorem checked67329 : checkPrefixCuts (2^48) 8828878849 10 Manual.Count131072.C067329.packed 64 cuts67329 = true := by
 decide +kernel
def cuts67330 : List PrefixCut := [⟨48,135970373,135970453⟩,
⟨64,182260529,182260636⟩]
theorem checked67330 : checkPrefixCuts (2^48) 8829009921 10 Manual.Count131072.C067330.packed 64 cuts67330 = true := by
 decide +kernel
def pointBounds67330 : List (Nat × Nat × Nat) := [(8829108224,115336531013258,115336920238807)]
theorem point_links_checked67330 : (cuts67330.take 1).map (fun c => (8829009921-1+2*2^10*c.k,115336395042885+c.lower,115336784268354+c.upper)) = pointBounds67330 := by
 decide +kernel
def cuts67331 : List PrefixCut := [⟨64,182321589,182321691⟩]
theorem checked67331 : checkPrefixCuts (2^48) 8829140993 10 Manual.Count131072.C067331.packed 64 cuts67331 = true := by
 decide +kernel
def cuts67332 : List PrefixCut := [⟨55,159588961,159589056⟩,
⟨64,185092400,185092510⟩]
theorem checked67332 : checkPrefixCuts (2^48) 8829272065 10 Manual.Count131072.C067332.packed 64 cuts67332 = true := by
 decide +kernel
def pointBounds67332 : List (Nat × Nat × Nat) := [(8829384704,115336919213964,115337308439737)]
theorem point_links_checked67332 : (cuts67332.take 1).map (fun c => (8829272065-1+2*2^10*c.k,115336759625003+c.lower,115337148850681+c.upper)) = pointBounds67332 := by
 decide +kernel
def cuts67333 : List PrefixCut := [⟨64,182475566,182475675⟩]
theorem checked67333 : checkPrefixCuts (2^48) 8829403137 10 Manual.Count131072.C067333.packed 64 cuts67333 = true := by
 decide +kernel
def cuts67334 : List PrefixCut := [⟨62,175140835,175140937⟩,
⟨64,180847055,180847161⟩]
theorem checked67334 : checkPrefixCuts (2^48) 8829534209 10 Manual.Count131072.C067334.packed 64 cuts67334 = true := by
 decide +kernel
def pointBounds67334 : List (Nat × Nat × Nat) := [(8829661184,115337302333804,115337691559803)]
theorem point_links_checked67334 : (cuts67334.take 1).map (fun c => (8829534209-1+2*2^10*c.k,115337127192969+c.lower,115337516418866+c.upper)) = pointBounds67334 := by
 decide +kernel
def cuts67335 : List PrefixCut := [⟨64,182788934,182789037⟩]
theorem checked67335 : checkPrefixCuts (2^48) 8829665281 10 Manual.Count131072.C067335.packed 64 cuts67335 = true := by
 decide +kernel
def cuts67336 : List PrefixCut := [⟨64,180937314,180937421⟩]
theorem checked67336 : checkPrefixCuts (2^48) 8829796353 10 Manual.Count131072.C067336.packed 64 cuts67336 = true := by
 decide +kernel
def cuts67337 : List PrefixCut := [⟨5,13898527,13898535⟩,
⟨64,184504861,184504967⟩]
theorem checked67337 : checkPrefixCuts (2^48) 8829927425 10 Manual.Count131072.C067337.packed 64 cuts67337 = true := by
 decide +kernel
def pointBounds67337 : List (Nat × Nat × Nat) := [(8829937664,115337685664799,115338074891020)]
theorem point_links_checked67337 : (cuts67337.take 1).map (fun c => (8829927425-1+2*2^10*c.k,115337671766272+c.lower,115338060992485+c.upper)) = pointBounds67337 := by
 decide +kernel
def cuts67338 : List PrefixCut := [⟨64,179529375,179529481⟩]
theorem checked67338 : checkPrefixCuts (2^48) 8830058497 10 Manual.Count131072.C067338.packed 64 cuts67338 = true := by
 decide +kernel
def cuts67339 : List PrefixCut := [⟨12,35000267,35000288⟩,
⟨64,182618697,182618810⟩]
theorem checked67339 : checkPrefixCuts (2^48) 8830189569 10 Manual.Count131072.C067339.packed 64 cuts67339 = true := by
 decide +kernel
def pointBounds67339 : List (Nat × Nat × Nat) := [(8830214144,115338070800775,115338460027221)]
theorem point_links_checked67339 : (cuts67339.take 1).map (fun c => (8830189569-1+2*2^10*c.k,115338035800508+c.lower,115338425026933+c.upper)) = pointBounds67339 := by
 decide +kernel
def cuts67340 : List PrefixCut := [⟨64,184687913,184688015⟩]
theorem checked67340 : checkPrefixCuts (2^48) 8830320641 10 Manual.Count131072.C067340.packed 64 cuts67340 = true := by
 decide +kernel
def cuts67341 : List PrefixCut := [⟨19,53231934,53231967⟩,
⟨64,179393866,179393972⟩]
theorem checked67341 : checkPrefixCuts (2^48) 8830451713 10 Manual.Count131072.C067341.packed 64 cuts67341 = true := by
 decide +kernel
def pointBounds67341 : List (Nat × Nat × Nat) := [(8830490624,115338456339052,115338845565725)]
theorem point_links_checked67341 : (cuts67341.take 1).map (fun c => (8830451713-1+2*2^10*c.k,115338403107118+c.lower,115338792333758+c.upper)) = pointBounds67341 := by
 decide +kernel
def cuts67342 : List PrefixCut := [⟨64,181909309,181909416⟩]
theorem checked67342 : checkPrefixCuts (2^48) 8830582785 10 Manual.Count131072.C067342.packed 64 cuts67342 = true := by
 decide +kernel
def cuts67343 : List PrefixCut := [⟨26,73853075,73853116⟩,
⟨64,182161616,182161722⟩]
theorem checked67343 : checkPrefixCuts (2^48) 8830713857 10 Manual.Count131072.C067343.packed 64 cuts67343 = true := by
 decide +kernel
def pointBounds67343 : List (Nat × Nat × Nat) := [(8830767104,115338838263368,115339227490262)]
theorem point_links_checked67343 : (cuts67343.take 1).map (fun c => (8830713857-1+2*2^10*c.k,115338764410293+c.lower,115339153637146+c.upper)) = pointBounds67343 := by
 decide +kernel
def cuts67344 : List PrefixCut := [⟨64,183401980,183402088⟩]
theorem checked67344 : checkPrefixCuts (2^48) 8830844929 10 Manual.Count131072.C067344.packed 64 cuts67344 = true := by
 decide +kernel
def cuts67345 : List PrefixCut := [⟨33,93707995,93708046⟩,
⟨64,184227971,184228073⟩]
theorem checked67345 : checkPrefixCuts (2^48) 8830976001 10 Manual.Count131072.C067345.packed 64 cuts67345 = true := by
 decide +kernel
def pointBounds67345 : List (Nat × Nat × Nat) := [(8831043584,115339223681884,115339612909002)]
theorem point_links_checked67345 : (cuts67345.take 1).map (fun c => (8830976001-1+2*2^10*c.k,115339129973889+c.lower,115339519200956+c.upper)) = pointBounds67345 := by
 decide +kernel
def cuts67346 : List PrefixCut := [⟨64,182759095,182759200⟩]
theorem checked67346 : checkPrefixCuts (2^48) 8831107073 10 Manual.Count131072.C067346.packed 64 cuts67346 = true := by
 decide +kernel
def cuts67347 : List PrefixCut := [⟨40,114039782,114039851⟩,
⟨64,183043220,183043326⟩]
theorem checked67347 : checkPrefixCuts (2^48) 8831238145 10 Manual.Count131072.C067347.packed 64 cuts67347 = true := by
 decide +kernel
def pointBounds67347 : List (Nat × Nat × Nat) := [(8831320064,115339611000737,115340000228080)]
theorem point_links_checked67347 : (cuts67347.take 1).map (fun c => (8831238145-1+2*2^10*c.k,115339496960955+c.lower,115339886188229+c.upper)) = pointBounds67347 := by
 decide +kernel
def cuts67348 : List PrefixCut := [⟨64,184920941,184921040⟩]
theorem checked67348 : checkPrefixCuts (2^48) 8831369217 10 Manual.Count131072.C067348.packed 64 cuts67348 = true := by
 decide +kernel
def cuts67349 : List PrefixCut := [⟨47,132330570,132330646⟩,
⟨64,179882527,179882632⟩]
theorem checked67349 : checkPrefixCuts (2^48) 8831500289 10 Manual.Count131072.C067349.packed 64 cuts67349 = true := by
 decide +kernel
def pointBounds67349 : List (Nat × Nat × Nat) := [(8831596544,115339997255686,115340386483241)]
theorem point_links_checked67349 : (cuts67349.take 1).map (fun c => (8831500289-1+2*2^10*c.k,115339864925116+c.lower,115340254152595+c.upper)) = pointBounds67349 := by
 decide +kernel
def cuts67350 : List PrefixCut := [⟨64,182557019,182557120⟩]
theorem checked67350 : checkPrefixCuts (2^48) 8831631361 10 Manual.Count131072.C067350.packed 64 cuts67350 = true := by
 decide +kernel
def cuts67351 : List PrefixCut := [⟨54,154221587,154221677⟩,
⟨64,182267462,182267569⟩]
theorem checked67351 : checkPrefixCuts (2^48) 8831762433 10 Manual.Count131072.C067351.packed 64 cuts67351 = true := by
 decide +kernel
def pointBounds67351 : List (Nat × Nat × Nat) := [(8831873024,115340381586249,115340770814024)]
theorem point_links_checked67351 : (cuts67351.take 1).map (fun c => (8831762433-1+2*2^10*c.k,115340227364662+c.lower,115340616592347+c.upper)) = pointBounds67351 := by
 decide +kernel
def cuts67352 : List PrefixCut := [⟨64,183698917,183699026⟩]
theorem checked67352 : checkPrefixCuts (2^48) 8831893505 10 Manual.Count131072.C067352.packed 64 cuts67352 = true := by
 decide +kernel
def cuts67353 : List PrefixCut := [⟨61,174836509,174836611⟩,
⟨64,183122538,183122644⟩]
theorem checked67353 : checkPrefixCuts (2^48) 8832024577 10 Manual.Count131072.C067353.packed 64 cuts67353 = true := by
 decide +kernel
def pointBounds67353 : List (Nat × Nat × Nat) := [(8832149504,115340768167550,115341157395553)]
theorem point_links_checked67353 : (cuts67353.take 1).map (fun c => (8832024577-1+2*2^10*c.k,115340593331041+c.lower,115340982558942+c.upper)) = pointBounds67353 := by
 decide +kernel
def cuts67354 : List PrefixCut := [⟨64,181558229,181558331⟩]
theorem checked67354 : checkPrefixCuts (2^48) 8832155649 10 Manual.Count131072.C067354.packed 64 cuts67354 = true := by
 decide +kernel
def cuts67355 : List PrefixCut := [⟨64,181396192,181396299⟩]
theorem checked67355 : checkPrefixCuts (2^48) 8832286721 10 Manual.Count131072.C067355.packed 64 cuts67355 = true := by
 decide +kernel
def cuts67356 : List PrefixCut := [⟨4,12460534,12460540⟩,
⟨64,182700103,182700212⟩]
theorem checked67356 : checkPrefixCuts (2^48) 8832417793 10 Manual.Count131072.C067356.packed 64 cuts67356 = true := by
 decide +kernel
def pointBounds67356 : List (Nat × Nat × Nat) := [(8832425984,115341151868534,115341541096756)]
theorem point_links_checked67356 : (cuts67356.take 1).map (fun c => (8832417793-1+2*2^10*c.k,115341139408000+c.lower,115341528636216+c.upper)) = pointBounds67356 := by
 decide +kernel
def cuts67357 : List PrefixCut := [⟨64,179861163,179861268⟩]
theorem checked67357 : checkPrefixCuts (2^48) 8832548865 10 Manual.Count131072.C067357.packed 64 cuts67357 = true := by
 decide +kernel
def cuts67358 : List PrefixCut := [⟨11,31325653,31325673⟩,
⟨64,180878242,180878350⟩]
theorem checked67358 : checkPrefixCuts (2^48) 8832679937 10 Manual.Count131072.C067358.packed 64 cuts67358 = true := by
 decide +kernel
def pointBounds67358 : List (Nat × Nat × Nat) := [(8832702464,115341533294919,115341922523369)]
theorem point_links_checked67358 : (cuts67358.take 1).map (fun c => (8832679937-1+2*2^10*c.k,115341501969266+c.lower,115341891197696+c.upper)) = pointBounds67358 := by
 decide +kernel
def cuts67359 : List PrefixCut := [⟨64,183265566,183265677⟩]
theorem checked67359 : checkPrefixCuts (2^48) 8832811009 10 Manual.Count131072.C067359.packed 64 cuts67359 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000229
