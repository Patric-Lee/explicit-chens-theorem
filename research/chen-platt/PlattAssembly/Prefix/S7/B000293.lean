import PlattAssemblyKernel
import PlattCertificates.Count131072.C069376
import PlattCertificates.Count131072.C069377
import PlattCertificates.Count131072.C069378
import PlattCertificates.Count131072.C069379
import PlattCertificates.Count131072.C069380
import PlattCertificates.Count131072.C069381
import PlattCertificates.Count131072.C069382
import PlattCertificates.Count131072.C069383
import PlattCertificates.Count131072.C069384
import PlattCertificates.Count131072.C069385
import PlattCertificates.Count131072.C069386
import PlattCertificates.Count131072.C069387
import PlattCertificates.Count131072.C069388
import PlattCertificates.Count131072.C069389
import PlattCertificates.Count131072.C069390
import PlattCertificates.Count131072.C069391
import PlattCertificates.Count131072.C069392
import PlattCertificates.Count131072.C069393
import PlattCertificates.Count131072.C069394
import PlattCertificates.Count131072.C069395
import PlattCertificates.Count131072.C069396
import PlattCertificates.Count131072.C069397
import PlattCertificates.Count131072.C069398
import PlattCertificates.Count131072.C069399
import PlattCertificates.Count131072.C069400
import PlattCertificates.Count131072.C069401
import PlattCertificates.Count131072.C069402
import PlattCertificates.Count131072.C069403
import PlattCertificates.Count131072.C069404
import PlattCertificates.Count131072.C069405
import PlattCertificates.Count131072.C069406
import PlattCertificates.Count131072.C069407
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000293
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69376 : List PrefixCut := [⟨38,104486923,104486986⟩,
⟨64,176392714,176392823⟩]
theorem checked69376 : checkPrefixCuts (2^48) 9097183233 10 Manual.Count131072.C069376.packed 64 cuts69376 = true := by
 decide +kernel
def pointBounds69376 : List (Nat × Nat × Nat) := [(9097261056,115704018917410,115704408358067)]
theorem point_links_checked69376 : (cuts69376.take 1).map (fun c => (9097183233-1+2*2^10*c.k,115703914430487+c.lower,115704303871081+c.upper)) = pointBounds69376 := by
 decide +kernel
def cuts69377 : List PrefixCut := [⟨64,178277518,178277625⟩]
theorem checked69377 : checkPrefixCuts (2^48) 9097314305 10 Manual.Count131072.C069377.packed 64 cuts69377 = true := by
 decide +kernel
def cuts69378 : List PrefixCut := [⟨49,134278825,134278906⟩,
⟨64,175211913,175212019⟩]
theorem checked69378 : checkPrefixCuts (2^48) 9097445377 10 Manual.Count131072.C069378.packed 64 cuts69378 = true := by
 decide +kernel
def pointBounds69378 : List (Nat × Nat × Nat) := [(9097545728,115704403379544,115704792820435)]
theorem point_links_checked69378 : (cuts69378.take 1).map (fun c => (9097445377-1+2*2^10*c.k,115704269100719+c.lower,115704658541529+c.upper)) = pointBounds69378 := by
 decide +kernel
def cuts69379 : List PrefixCut := [⟨64,182201687,182201795⟩]
theorem checked69379 : checkPrefixCuts (2^48) 9097576449 10 Manual.Count131072.C069379.packed 64 cuts69379 = true := by
 decide +kernel
def cuts69380 : List PrefixCut := [⟨60,165770590,165770687⟩,
⟨64,176815695,176815799⟩]
theorem checked69380 : checkPrefixCuts (2^48) 9097707521 10 Manual.Count131072.C069380.packed 64 cuts69380 = true := by
 decide +kernel
def pointBounds69380 : List (Nat × Nat × Nat) := [(9097830400,115704792284909,115705181726030)]
theorem point_links_checked69380 : (cuts69380.take 1).map (fun c => (9097707521-1+2*2^10*c.k,115704626514319+c.lower,115705015955343+c.upper)) = pointBounds69380 := by
 decide +kernel
def cuts69381 : List PrefixCut := [⟨64,178947891,178948000⟩]
theorem checked69381 : checkPrefixCuts (2^48) 9097838593 10 Manual.Count131072.C069381.packed 64 cuts69381 = true := by
 decide +kernel
def cuts69382 : List PrefixCut := [⟨64,176222783,176222887⟩]
theorem checked69382 : checkPrefixCuts (2^48) 9097969665 10 Manual.Count131072.C069382.packed 64 cuts69382 = true := by
 decide +kernel
def cuts69383 : List PrefixCut := [⟨7,19552652,19552663⟩,
⟨64,178788062,178788162⟩]
theorem checked69383 : checkPrefixCuts (2^48) 9098100737 10 Manual.Count131072.C069383.packed 64 cuts69383 = true := by
 decide +kernel
def pointBounds69383 : List (Nat × Nat × Nat) := [(9098115072,115705178053340,115705567494692)]
theorem point_links_checked69383 : (cuts69383.take 1).map (fun c => (9098100737-1+2*2^10*c.k,115705158500688+c.lower,115705547942029+c.upper)) = pointBounds69383 := by
 decide +kernel
def cuts69384 : List PrefixCut := [⟨64,177795490,177795596⟩]
theorem checked69384 : checkPrefixCuts (2^48) 9098231809 10 Manual.Count131072.C069384.packed 64 cuts69384 = true := by
 decide +kernel
def cuts69385 : List PrefixCut := [⟨18,49034846,49034872⟩,
⟨64,177081382,177081482⟩]
theorem checked69385 : checkPrefixCuts (2^48) 9098362881 10 Manual.Count131072.C069385.packed 64 cuts69385 = true := by
 decide +kernel
def pointBounds69385 : List (Nat × Nat × Nat) := [(9098399744,115705564119086,115705953560659)]
theorem point_links_checked69385 : (cuts69385.take 1).map (fun c => (9098362881-1+2*2^10*c.k,115705515084240+c.lower,115705904525787+c.upper)) = pointBounds69385 := by
 decide +kernel
def cuts69386 : List PrefixCut := [⟨64,179244376,179244479⟩]
theorem checked69386 : checkPrefixCuts (2^48) 9098493953 10 Manual.Count131072.C069386.packed 64 cuts69386 = true := by
 decide +kernel
def cuts69387 : List PrefixCut := [⟨29,79659891,79659937⟩,
⟨64,175993527,175993628⟩]
theorem checked69387 : checkPrefixCuts (2^48) 9098625025 10 Manual.Count131072.C069387.packed 64 cuts69387 = true := by
 decide +kernel
def pointBounds69387 : List (Nat × Nat × Nat) := [(9098684416,115705951069889,115706340511685)]
theorem point_links_checked69387 : (cuts69387.take 1).map (fun c => (9098625025-1+2*2^10*c.k,115705871409998+c.lower,115706260851748+c.upper)) = pointBounds69387 := by
 decide +kernel
def cuts69388 : List PrefixCut := [⟨64,175960049,175960158⟩]
theorem checked69388 : checkPrefixCuts (2^48) 9098756097 10 Manual.Count131072.C069388.packed 64 cuts69388 = true := by
 decide +kernel
def cuts69389 : List PrefixCut := [⟨40,109045691,109045756⟩,
⟨64,174781984,174782091⟩]
theorem checked69389 : checkPrefixCuts (2^48) 9098887169 10 Manual.Count131072.C069389.packed 64 cuts69389 = true := by
 decide +kernel
def pointBounds69389 : List (Nat × Nat × Nat) := [(9098969088,115706332409265,115706721851290)]
theorem point_links_checked69389 : (cuts69389.take 1).map (fun c => (9098887169-1+2*2^10*c.k,115706223363574+c.lower,115706612805534+c.upper)) = pointBounds69389 := by
 decide +kernel
def cuts69390 : List PrefixCut := [⟨64,176016849,176016954⟩]
theorem checked69390 : checkPrefixCuts (2^48) 9099018241 10 Manual.Count131072.C069390.packed 64 cuts69390 = true := by
 decide +kernel
def cuts69391 : List PrefixCut := [⟨51,139543370,139543453⟩,
⟨64,176014319,176014423⟩]
theorem checked69391 : checkPrefixCuts (2^48) 9099149313 10 Manual.Count131072.C069391.packed 64 cuts69391 = true := by
 decide +kernel
def pointBounds69391 : List (Nat × Nat × Nat) := [(9099253760,115706713705777,115707103148032)]
theorem point_links_checked69391 : (cuts69391.take 1).map (fun c => (9099149313-1+2*2^10*c.k,115706574162407+c.lower,115706963604579+c.upper)) = pointBounds69391 := by
 decide +kernel
def cuts69392 : List PrefixCut := [⟨64,175980856,175980960⟩]
theorem checked69392 : checkPrefixCuts (2^48) 9099280385 10 Manual.Count131072.C069392.packed 64 cuts69392 = true := by
 decide +kernel
def cuts69393 : List PrefixCut := [⟨62,172235449,172235547⟩,
⟨64,177246573,177246675⟩]
theorem checked69393 : checkPrefixCuts (2^48) 9099411457 10 Manual.Count131072.C069393.packed 64 cuts69393 = true := by
 decide +kernel
def pointBounds69393 : List (Nat × Nat × Nat) := [(9099538432,115707098393031,115707487835509)]
theorem point_links_checked69393 : (cuts69393.take 1).map (fun c => (9099411457-1+2*2^10*c.k,115706926157582+c.lower,115707315599962+c.upper)) = pointBounds69393 := by
 decide +kernel
def cuts69394 : List PrefixCut := [⟨64,180584743,180584848⟩]
theorem checked69394 : checkPrefixCuts (2^48) 9099542529 10 Manual.Count131072.C069394.packed 64 cuts69394 = true := by
 decide +kernel
def cuts69395 : List PrefixCut := [⟨64,176035112,176035215⟩]
theorem checked69395 : checkPrefixCuts (2^48) 9099673601 10 Manual.Count131072.C069395.packed 64 cuts69395 = true := by
 decide +kernel
def cuts69396 : List PrefixCut := [⟨9,24652755,24652771⟩,
⟨64,176249103,176249204⟩]
theorem checked69396 : checkPrefixCuts (2^48) 9099804673 10 Manual.Count131072.C069396.packed 64 cuts69396 = true := by
 decide +kernel
def pointBounds69396 : List (Nat × Nat × Nat) := [(9099823104,115707484676765,115707874119471)]
theorem point_links_checked69396 : (cuts69396.take 1).map (fun c => (9099804673-1+2*2^10*c.k,115707460024010+c.lower,115707849466700+c.upper)) = pointBounds69396 := by
 decide +kernel
def cuts69397 : List PrefixCut := [⟨64,175535145,175535251⟩]
theorem checked69397 : checkPrefixCuts (2^48) 9099935745 10 Manual.Count131072.C069397.packed 64 cuts69397 = true := by
 decide +kernel
def cuts69398 : List PrefixCut := [⟨20,55119060,55119092⟩,
⟨64,176553326,176553436⟩]
theorem checked69398 : checkPrefixCuts (2^48) 9100066817 10 Manual.Count131072.C069398.packed 64 cuts69398 = true := by
 decide +kernel
def pointBounds69398 : List (Nat × Nat × Nat) := [(9100107776,115707866927318,115708256370247)]
theorem point_links_checked69398 : (cuts69398.take 1).map (fun c => (9100066817-1+2*2^10*c.k,115707811808258+c.lower,115708201251155+c.upper)) = pointBounds69398 := by
 decide +kernel
def cuts69399 : List PrefixCut := [⟨64,177138470,177138576⟩]
theorem checked69399 : checkPrefixCuts (2^48) 9100197889 10 Manual.Count131072.C069399.packed 64 cuts69399 = true := by
 decide +kernel
def cuts69400 : List PrefixCut := [⟨31,85923767,85923814⟩,
⟨64,177878241,177878334⟩]
theorem checked69400 : checkPrefixCuts (2^48) 9100328961 10 Manual.Count131072.C069400.packed 64 cuts69400 = true := by
 decide +kernel
def pointBounds69400 : List (Nat × Nat × Nat) := [(9100392448,115708251423821,115708640866981)]
theorem point_links_checked69400 : (cuts69400.take 1).map (fun c => (9100328961-1+2*2^10*c.k,115708165500054+c.lower,115708554943167+c.upper)) = pointBounds69400 := by
 decide +kernel
def cuts69401 : List PrefixCut := [⟨64,176143621,176143729⟩]
theorem checked69401 : checkPrefixCuts (2^48) 9100460033 10 Manual.Count131072.C069401.packed 64 cuts69401 = true := by
 decide +kernel
def cuts69402 : List PrefixCut := [⟨42,115334808,115334875⟩,
⟨64,176326655,176326759⟩]
theorem checked69402 : checkPrefixCuts (2^48) 9100591105 10 Manual.Count131072.C069402.packed 64 cuts69402 = true := by
 decide +kernel
def pointBounds69402 : List (Nat × Nat × Nat) := [(9100677120,115708634856724,115709024300105)]
theorem point_links_checked69402 : (cuts69402.take 1).map (fun c => (9100591105-1+2*2^10*c.k,115708519521916+c.lower,115708908965230+c.upper)) = pointBounds69402 := by
 decide +kernel
def cuts69403 : List PrefixCut := [⟨64,178458195,178458285⟩]
theorem checked69403 : checkPrefixCuts (2^48) 9100722177 10 Manual.Count131072.C069403.packed 64 cuts69403 = true := by
 decide +kernel
def cuts69404 : List PrefixCut := [⟨53,146692562,146692650⟩,
⟨64,177032931,177033036⟩]
theorem checked69404 : checkPrefixCuts (2^48) 9100853249 10 Manual.Count131072.C069404.packed 64 cuts69404 = true := by
 decide +kernel
def pointBounds69404 : List (Nat × Nat × Nat) := [(9100961792,115709020999328,115709410442924)]
theorem point_links_checked69404 : (cuts69404.take 1).map (fun c => (9100853249-1+2*2^10*c.k,115708874306766+c.lower,115709263750274+c.upper)) = pointBounds69404 := by
 decide +kernel
def cuts69405 : List PrefixCut := [⟨64,176906669,176906772⟩]
theorem checked69405 : checkPrefixCuts (2^48) 9100984321 10 Manual.Count131072.C069405.packed 64 cuts69405 = true := by
 decide +kernel
def cuts69406 : List PrefixCut := [⟨64,177182469,177182572⟩]
theorem checked69406 : checkPrefixCuts (2^48) 9101115393 10 Manual.Count131072.C069406.packed 64 cuts69406 = true := by
 decide +kernel
def pointBounds69406 : List (Nat × Nat × Nat) := [(9101246464,115709405428835,115709794872654)]
theorem point_links_checked69406 : (cuts69406.take 1).map (fun c => (9101115393-1+2*2^10*c.k,115709228246366+c.lower,115709617690082+c.upper)) = pointBounds69406 := by
 decide +kernel
def cuts69407 : List PrefixCut := [⟨64,174705774,174705880⟩]
theorem checked69407 : checkPrefixCuts (2^48) 9101246465 10 Manual.Count131072.C069407.packed 64 cuts69407 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000293
