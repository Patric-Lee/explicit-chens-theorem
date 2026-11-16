import PlattAssemblyKernel
import PlattCertificates.Count131072.C059344
import PlattCertificates.Count131072.C059345
import PlattCertificates.Count131072.C059346
import PlattCertificates.Count131072.C059347
import PlattCertificates.Count131072.C059348
import PlattCertificates.Count131072.C059349
import PlattCertificates.Count131072.C059350
import PlattCertificates.Count131072.C059351
import PlattCertificates.Count131072.C059352
import PlattCertificates.Count131072.C059353
import PlattCertificates.Count131072.C059354
import PlattCertificates.Count131072.C059355
import PlattCertificates.Count131072.C059356
import PlattCertificates.Count131072.C059357
import PlattCertificates.Count131072.C059358
import PlattCertificates.Count131072.C059359
import PlattCertificates.Count131072.C059360
import PlattCertificates.Count131072.C059361
import PlattCertificates.Count131072.C059362
import PlattCertificates.Count131072.C059363
import PlattCertificates.Count131072.C059364
import PlattCertificates.Count131072.C059365
import PlattCertificates.Count131072.C059366
import PlattCertificates.Count131072.C059367
import PlattCertificates.Count131072.C059368
import PlattCertificates.Count131072.C059369
import PlattCertificates.Count131072.C059370
import PlattCertificates.Count131072.C059371
import PlattCertificates.Count131072.C059372
import PlattCertificates.Count131072.C059373
import PlattCertificates.Count131072.C059374
import PlattCertificates.Count131072.C059375
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000292
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59344 : List PrefixCut := [⟨64,208619567,208619681⟩]
theorem checked59344 : checkPrefixCuts (2^48) 7782268929 10 Manual.Count131072.C059344.packed 64 cuts59344 = true := by
 decide +kernel
def cuts59345 : List PrefixCut := [⟨27,87743583,87743633⟩,
⟨64,206084297,206084414⟩]
theorem checked59345 : checkPrefixCuts (2^48) 7782400001 10 Manual.Count131072.C059345.packed 64 cuts59345 = true := by
 decide +kernel
def pointBounds59345 : List (Nat × Nat × Nat) := [(7782455296,113781318409951,113781706739896)]
theorem point_links_checked59345 : (cuts59345.take 1).map (fun c => (7782400001-1+2*2^10*c.k,113781230666368+c.lower,113781618996263+c.upper)) = pointBounds59345 := by
 decide +kernel
def cuts59346 : List PrefixCut := [⟨64,210131563,210131683⟩]
theorem checked59346 : checkPrefixCuts (2^48) 7782531073 10 Manual.Count131072.C059346.packed 64 cuts59346 = true := by
 decide +kernel
def cuts59347 : List PrefixCut := [⟨18,58734935,58734970⟩,
⟨64,209368515,209368634⟩]
theorem checked59347 : checkPrefixCuts (2^48) 7782662145 10 Manual.Count131072.C059347.packed 64 cuts59347 = true := by
 decide +kernel
def pointBounds59347 : List (Nat × Nat × Nat) := [(7782699008,113781705617163,113782093947330)]
theorem point_links_checked59347 : (cuts59347.take 1).map (fun c => (7782662145-1+2*2^10*c.k,113781646882228+c.lower,113782035212360+c.upper)) = pointBounds59347 := by
 decide +kernel
def cuts59348 : List PrefixCut := [⟨64,210486169,210486285⟩]
theorem checked59348 : checkPrefixCuts (2^48) 7782793217 10 Manual.Count131072.C059348.packed 64 cuts59348 = true := by
 decide +kernel
def cuts59349 : List PrefixCut := [⟨9,28390041,28390056⟩,
⟨64,205021625,205021737⟩]
theorem checked59349 : checkPrefixCuts (2^48) 7782924289 10 Manual.Count131072.C059349.packed 64 cuts59349 = true := by
 decide +kernel
def pointBounds59349 : List (Nat × Nat × Nat) := [(7782942720,113782095126953,113782483457335)]
theorem point_links_checked59349 : (cuts59349.take 1).map (fun c => (7782924289-1+2*2^10*c.k,113782066736912+c.lower,113782455067279+c.upper)) = pointBounds59349 := by
 decide +kernel
def cuts59350 : List PrefixCut := [⟨64,209900420,209900537⟩]
theorem checked59350 : checkPrefixCuts (2^48) 7783055361 10 Manual.Count131072.C059350.packed 64 cuts59350 = true := by
 decide +kernel
def pointBounds59350 : List (Nat × Nat × Nat) := [(7783186432,113782481658957,113782869989553)]
theorem point_links_checked59350 : (cuts59350.take 1).map (fun c => (7783055361-1+2*2^10*c.k,113782271758537+c.lower,113782660089016+c.upper)) = pointBounds59350 := by
 decide +kernel
def cuts59351 : List PrefixCut := [⟨64,204399930,204400053⟩]
theorem checked59351 : checkPrefixCuts (2^48) 7783186433 10 Manual.Count131072.C059351.packed 64 cuts59351 = true := by
 decide +kernel
def cuts59352 : List PrefixCut := [⟨55,176297596,176297692⟩,
⟨64,207506530,207506643⟩]
theorem checked59352 : checkPrefixCuts (2^48) 7783317505 10 Manual.Count131072.C059352.packed 64 cuts59352 = true := by
 decide +kernel
def pointBounds59352 : List (Nat × Nat × Nat) := [(7783430144,113782862356483,113783250687298)]
theorem point_links_checked59352 : (cuts59352.take 1).map (fun c => (7783317505-1+2*2^10*c.k,113782686058887+c.lower,113783074389606+c.upper)) = pointBounds59352 := by
 decide +kernel
def cuts59353 : List PrefixCut := [⟨64,206598979,206599091⟩]
theorem checked59353 : checkPrefixCuts (2^48) 7783448577 10 Manual.Count131072.C059353.packed 64 cuts59353 = true := by
 decide +kernel
def cuts59354 : List PrefixCut := [⟨46,149603999,149604086⟩,
⟨64,208403620,208403743⟩]
theorem checked59354 : checkPrefixCuts (2^48) 7783579649 10 Manual.Count131072.C059354.packed 64 cuts59354 = true := by
 decide +kernel
def pointBounds59354 : List (Nat × Nat × Nat) := [(7783673856,113783249768395,113783638099426)]
theorem point_links_checked59354 : (cuts59354.take 1).map (fun c => (7783579649-1+2*2^10*c.k,113783100164396+c.lower,113783488495340+c.upper)) = pointBounds59354 := by
 decide +kernel
def cuts59355 : List PrefixCut := [⟨64,209267995,209268117⟩]
theorem checked59355 : checkPrefixCuts (2^48) 7783710721 10 Manual.Count131072.C059355.packed 64 cuts59355 = true := by
 decide +kernel
def cuts59356 : List PrefixCut := [⟨37,117234808,117234875⟩,
⟨64,206371564,206371679⟩]
theorem checked59356 : checkPrefixCuts (2^48) 7783841793 10 Manual.Count131072.C059356.packed 64 cuts59356 = true := by
 decide +kernel
def pointBounds59356 : List (Nat × Nat × Nat) := [(7783917568,113783635070819,113784023402075)]
theorem point_links_checked59356 : (cuts59356.take 1).map (fun c => (7783841793-1+2*2^10*c.k,113783517836011+c.lower,113783906167200+c.upper)) = pointBounds59356 := by
 decide +kernel
def cuts59357 : List PrefixCut := [⟨64,210454225,210454346⟩]
theorem checked59357 : checkPrefixCuts (2^48) 7783972865 10 Manual.Count131072.C059357.packed 64 cuts59357 = true := by
 decide +kernel
def cuts59358 : List PrefixCut := [⟨28,92063573,92063625⟩,
⟨64,209040468,209040586⟩]
theorem checked59358 : checkPrefixCuts (2^48) 7784103937 10 Manual.Count131072.C059358.packed 64 cuts59358 = true := by
 decide +kernel
def pointBounds59358 : List (Nat × Nat × Nat) := [(7784161280,113784026725373,113784415056850)]
theorem point_links_checked59358 : (cuts59358.take 1).map (fun c => (7784103937-1+2*2^10*c.k,113783934661800+c.lower,113784322993225+c.upper)) = pointBounds59358 := by
 decide +kernel
def cuts59359 : List PrefixCut := [⟨64,208205276,208205392⟩]
theorem checked59359 : checkPrefixCuts (2^48) 7784235009 10 Manual.Count131072.C059359.packed 64 cuts59359 = true := by
 decide +kernel
def cuts59360 : List PrefixCut := [⟨19,61867898,61867931⟩,
⟨64,207261652,207261768⟩]
theorem checked59360 : checkPrefixCuts (2^48) 7784366081 10 Manual.Count131072.C059360.packed 64 cuts59360 = true := by
 decide +kernel
def pointBounds59360 : List (Nat × Nat × Nat) := [(7784404992,113784413775442,113784802107134)]
theorem point_links_checked59360 : (cuts59360.take 1).map (fun c => (7784366081-1+2*2^10*c.k,113784351907544+c.lower,113784740239203+c.upper)) = pointBounds59360 := by
 decide +kernel
def cuts59361 : List PrefixCut := [⟨64,207221999,207222113⟩]
theorem checked59361 : checkPrefixCuts (2^48) 7784497153 10 Manual.Count131072.C059361.packed 64 cuts59361 = true := by
 decide +kernel
def cuts59362 : List PrefixCut := [⟨10,33662852,33662870⟩,
⟨64,207724731,207724852⟩]
theorem checked59362 : checkPrefixCuts (2^48) 7784628225 10 Manual.Count131072.C059362.packed 64 cuts59362 = true := by
 decide +kernel
def pointBounds59362 : List (Nat × Nat × Nat) := [(7784648704,113784800054047,113785188385954)]
theorem point_links_checked59362 : (cuts59362.take 1).map (fun c => (7784628225-1+2*2^10*c.k,113784766391195+c.lower,113785154723084+c.upper)) = pointBounds59362 := by
 decide +kernel
def cuts59363 : List PrefixCut := [⟨64,206889617,206889735⟩]
theorem checked59363 : checkPrefixCuts (2^48) 7784759297 10 Manual.Count131072.C059363.packed 64 cuts59363 = true := by
 decide +kernel
def cuts59364 : List PrefixCut := [⟨1,3579500,3579501⟩,
⟨64,210176349,210176470⟩]
theorem checked59364 : checkPrefixCuts (2^48) 7784890369 10 Manual.Count131072.C059364.packed 64 cuts59364 = true := by
 decide +kernel
def pointBounds59364 : List (Nat × Nat × Nat) := [(7784892416,113785184585043,113785572917172)]
theorem point_links_checked59364 : (cuts59364.take 1).map (fun c => (7784890369-1+2*2^10*c.k,113785181005543+c.lower,113785569337671+c.upper)) = pointBounds59364 := by
 decide +kernel
def cuts59365 : List PrefixCut := [⟨56,182224681,182224787⟩,
⟨64,208979669,208979788⟩]
theorem checked59365 : checkPrefixCuts (2^48) 7785021441 10 Manual.Count131072.C059365.packed 64 cuts59365 = true := by
 decide +kernel
def pointBounds59365 : List (Nat × Nat × Nat) := [(7785136128,113785573406573,113785961738928)]
theorem point_links_checked59365 : (cuts59365.take 1).map (fun c => (7785021441-1+2*2^10*c.k,113785391181892+c.lower,113785779514141+c.upper)) = pointBounds59365 := by
 decide +kernel
def cuts59366 : List PrefixCut := [⟨64,208614593,208614712⟩]
theorem checked59366 : checkPrefixCuts (2^48) 7785152513 10 Manual.Count131072.C059366.packed 64 cuts59366 = true := by
 decide +kernel
def cuts59367 : List PrefixCut := [⟨47,153439768,153439855⟩,
⟨64,207164924,207165040⟩]
theorem checked59367 : checkPrefixCuts (2^48) 7785283585 10 Manual.Count131072.C059367.packed 64 cuts59367 = true := by
 decide +kernel
def pointBounds59367 : List (Nat × Nat × Nat) := [(7785379840,113785962215922,113786350548496)]
theorem point_links_checked59367 : (cuts59367.take 1).map (fun c => (7785283585-1+2*2^10*c.k,113785808776154+c.lower,113786197108641+c.upper)) = pointBounds59367 := by
 decide +kernel
def cuts59368 : List PrefixCut := [⟨64,204847596,204847714⟩]
theorem checked59368 : checkPrefixCuts (2^48) 7785414657 10 Manual.Count131072.C059368.packed 64 cuts59368 = true := by
 decide +kernel
def cuts59369 : List PrefixCut := [⟨38,124765180,124765253⟩,
⟨64,209182520,209182640⟩]
theorem checked59369 : checkPrefixCuts (2^48) 7785545729 10 Manual.Count131072.C059369.packed 64 cuts59369 = true := by
 decide +kernel
def pointBounds59369 : List (Nat × Nat × Nat) := [(7785623552,113786345553854,113786733886648)]
theorem point_links_checked59369 : (cuts59369.take 1).map (fun c => (7785545729-1+2*2^10*c.k,113786220788674+c.lower,113786609121395+c.upper)) = pointBounds59369 := by
 decide +kernel
def cuts59370 : List PrefixCut := [⟨64,209359767,209359888⟩]
theorem checked59370 : checkPrefixCuts (2^48) 7785676801 10 Manual.Count131072.C059370.packed 64 cuts59370 = true := by
 decide +kernel
def cuts59371 : List PrefixCut := [⟨29,95369414,95369470⟩,
⟨64,208524740,208524858⟩]
theorem checked59371 : checkPrefixCuts (2^48) 7785807873 10 Manual.Count131072.C059371.packed 64 cuts59371 = true := by
 decide +kernel
def pointBounds59371 : List (Nat × Nat × Nat) := [(7785867264,113786734700375,113787123033393)]
theorem point_links_checked59371 : (cuts59371.take 1).map (fun c => (7785807873-1+2*2^10*c.k,113786639330961+c.lower,113787027663923+c.upper)) = pointBounds59371 := by
 decide +kernel
def cuts59372 : List PrefixCut := [⟨64,207075185,207075301⟩]
theorem checked59372 : checkPrefixCuts (2^48) 7785938945 10 Manual.Count131072.C059372.packed 64 cuts59372 = true := by
 decide +kernel
def cuts59373 : List PrefixCut := [⟨20,64312618,64312657⟩,
⟨64,209168430,209168552⟩]
theorem checked59373 : checkPrefixCuts (2^48) 7786070017 10 Manual.Count131072.C059373.packed 64 cuts59373 = true := by
 decide +kernel
def pointBounds59373 : List (Nat × Nat × Nat) := [(7786110976,113787119243504,113787507576739)]
theorem point_links_checked59373 : (cuts59373.take 1).map (fun c => (7786070017-1+2*2^10*c.k,113787054930886+c.lower,113787443264082+c.upper)) = pointBounds59373 := by
 decide +kernel
def cuts59374 : List PrefixCut := [⟨64,205658341,205658458⟩]
theorem checked59374 : checkPrefixCuts (2^48) 7786201089 10 Manual.Count131072.C059374.packed 64 cuts59374 = true := by
 decide +kernel
def cuts59375 : List PrefixCut := [⟨11,35354520,35354541⟩,
⟨64,210390474,210390594⟩]
theorem checked59375 : checkPrefixCuts (2^48) 7786332161 10 Manual.Count131072.C059375.packed 64 cuts59375 = true := by
 decide +kernel
def pointBounds59375 : List (Nat × Nat × Nat) := [(7786354688,113787505112177,113787893445633)]
theorem point_links_checked59375 : (cuts59375.take 1).map (fun c => (7786332161-1+2*2^10*c.k,113787469757657+c.lower,113787858091092+c.upper)) = pointBounds59375 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000292
