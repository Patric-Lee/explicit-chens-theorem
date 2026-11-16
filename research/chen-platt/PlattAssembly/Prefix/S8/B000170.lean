import PlattAssemblyKernel
import PlattCertificates.Count131072.C075440
import PlattCertificates.Count131072.C075441
import PlattCertificates.Count131072.C075442
import PlattCertificates.Count131072.C075443
import PlattCertificates.Count131072.C075444
import PlattCertificates.Count131072.C075445
import PlattCertificates.Count131072.C075446
import PlattCertificates.Count131072.C075447
import PlattCertificates.Count131072.C075448
import PlattCertificates.Count131072.C075449
import PlattCertificates.Count131072.C075450
import PlattCertificates.Count131072.C075451
import PlattCertificates.Count131072.C075452
import PlattCertificates.Count131072.C075453
import PlattCertificates.Count131072.C075454
import PlattCertificates.Count131072.C075455
import PlattCertificates.Count131072.C075456
import PlattCertificates.Count131072.C075457
import PlattCertificates.Count131072.C075458
import PlattCertificates.Count131072.C075459
import PlattCertificates.Count131072.C075460
import PlattCertificates.Count131072.C075461
import PlattCertificates.Count131072.C075462
import PlattCertificates.Count131072.C075463
import PlattCertificates.Count131072.C075464
import PlattCertificates.Count131072.C075465
import PlattCertificates.Count131072.C075466
import PlattCertificates.Count131072.C075467
import PlattCertificates.Count131072.C075468
import PlattCertificates.Count131072.C075469
import PlattCertificates.Count131072.C075470
import PlattCertificates.Count131072.C075471
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000170
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75440 : List PrefixCut := [⟨64,160284770,160284864⟩]
theorem checked75440 : checkPrefixCuts (2^48) 9892003841 10 Manual.Count131072.C075440.packed 64 cuts75440 = true := by
 decide +kernel
def cuts75441 : List PrefixCut := [⟨64,161676895,161676990⟩]
theorem checked75441 : checkPrefixCuts (2^48) 9892134913 10 Manual.Count131072.C075441.packed 64 cuts75441 = true := by
 decide +kernel
def cuts75442 : List PrefixCut := [⟨23,57107113,57107149⟩,
⟨64,161162585,161162682⟩]
theorem checked75442 : checkPrefixCuts (2^48) 9892265985 10 Manual.Count131072.C075442.packed 64 cuts75442 = true := by
 decide +kernel
def pointBounds75442 : List (Nat × Nat × Nat) := [(9892313088,116730618083252,116731008133778)]
theorem point_links_checked75442 : (cuts75442.take 1).map (fun c => (9892265985-1+2*2^10*c.k,116730560976139+c.lower,116730951026629+c.upper)) = pointBounds75442 := by
 decide +kernel
def cuts75443 : List PrefixCut := [⟨64,163977349,163977447⟩]
theorem checked75443 : checkPrefixCuts (2^48) 9892397057 10 Manual.Count131072.C075443.packed 64 cuts75443 = true := by
 decide +kernel
def cuts75444 : List PrefixCut := [⟨46,116913978,116914051⟩,
⟨64,163804452,163804553⟩]
theorem checked75444 : checkPrefixCuts (2^48) 9892528129 10 Manual.Count131072.C075444.packed 64 cuts75444 = true := by
 decide +kernel
def pointBounds75444 : List (Nat × Nat × Nat) := [(9892622336,116731003030051,116731393080809)]
theorem point_links_checked75444 : (cuts75444.take 1).map (fun c => (9892528129-1+2*2^10*c.k,116730886116073+c.lower,116731276166758+c.upper)) = pointBounds75444 := by
 decide +kernel
def cuts75445 : List PrefixCut := [⟨64,161184647,161184743⟩]
theorem checked75445 : checkPrefixCuts (2^48) 9892659201 10 Manual.Count131072.C075445.packed 64 cuts75445 = true := by
 decide +kernel
def cuts75446 : List PrefixCut := [⟨64,162377509,162377608⟩]
theorem checked75446 : checkPrefixCuts (2^48) 9892790273 10 Manual.Count131072.C075446.packed 64 cuts75446 = true := by
 decide +kernel
def cuts75447 : List PrefixCut := [⟨5,12376679,12376688⟩,
⟨64,160099186,160099288⟩]
theorem checked75447 : checkPrefixCuts (2^48) 9892921345 10 Manual.Count131072.C075447.packed 64 cuts75447 = true := by
 decide +kernel
def pointBounds75447 : List (Nat × Nat × Nat) := [(9892931584,116731385859360,116731775910350)]
theorem point_links_checked75447 : (cuts75447.take 1).map (fun c => (9892921345-1+2*2^10*c.k,116731373482681+c.lower,116731763533662+c.upper)) = pointBounds75447 := by
 decide +kernel
def cuts75448 : List PrefixCut := [⟨64,161178231,161178330⟩]
theorem checked75448 : checkPrefixCuts (2^48) 9893052417 10 Manual.Count131072.C075448.packed 64 cuts75448 = true := by
 decide +kernel
def cuts75449 : List PrefixCut := [⟨28,72095628,72095672⟩,
⟨64,162940077,162940173⟩]
theorem checked75449 : checkPrefixCuts (2^48) 9893183489 10 Manual.Count131072.C075449.packed 64 cuts75449 = true := by
 decide +kernel
def pointBounds75449 : List (Nat × Nat × Nat) := [(9893240832,116731766855726,116732156906952)]
theorem point_links_checked75449 : (cuts75449.take 1).map (fun c => (9893183489-1+2*2^10*c.k,116731694760098+c.lower,116732084811280+c.upper)) = pointBounds75449 := by
 decide +kernel
def cuts75450 : List PrefixCut := [⟨64,160775658,160775757⟩]
theorem checked75450 : checkPrefixCuts (2^48) 9893314561 10 Manual.Count131072.C075450.packed 64 cuts75450 = true := by
 decide +kernel
def cuts75451 : List PrefixCut := [⟨51,129677347,129677421⟩,
⟨64,161655487,161655583⟩]
theorem checked75451 : checkPrefixCuts (2^48) 9893445633 10 Manual.Count131072.C075451.packed 64 cuts75451 = true := by
 decide +kernel
def pointBounds75451 : List (Nat × Nat × Nat) := [(9893550080,116732148153180,116732538204631)]
theorem point_links_checked75451 : (cuts75451.take 1).map (fun c => (9893445633-1+2*2^10*c.k,116732018475833+c.lower,116732408527210+c.upper)) = pointBounds75451 := by
 decide +kernel
def cuts75452 : List PrefixCut := [⟨64,162193893,162193994⟩]
theorem checked75452 : checkPrefixCuts (2^48) 9893576705 10 Manual.Count131072.C075452.packed 64 cuts75452 = true := by
 decide +kernel
def cuts75453 : List PrefixCut := [⟨64,161224446,161224545⟩]
theorem checked75453 : checkPrefixCuts (2^48) 9893707777 10 Manual.Count131072.C075453.packed 64 cuts75453 = true := by
 decide +kernel
def cuts75454 : List PrefixCut := [⟨10,25803681,25803695⟩,
⟨64,166798378,166798481⟩]
theorem checked75454 : checkPrefixCuts (2^48) 9893838849 10 Manual.Count131072.C075454.packed 64 cuts75454 = true := by
 decide +kernel
def pointBounds75454 : List (Nat × Nat × Nat) := [(9893859328,116732529353340,116732919405027)]
theorem point_links_checked75454 : (cuts75454.take 1).map (fun c => (9893838849-1+2*2^10*c.k,116732503549659+c.lower,116732893601332+c.upper)) = pointBounds75454 := by
 decide +kernel
def cuts75455 : List PrefixCut := [⟨64,161988305,161988402⟩]
theorem checked75455 : checkPrefixCuts (2^48) 9893969921 10 Manual.Count131072.C075455.packed 64 cuts75455 = true := by
 decide +kernel
def cuts75456 : List PrefixCut := [⟨33,82842501,82842551⟩,
⟨64,159368891,159368988⟩]
theorem checked75456 : checkPrefixCuts (2^48) 9894100993 10 Manual.Count131072.C075456.packed 64 cuts75456 = true := by
 decide +kernel
def pointBounds75456 : List (Nat × Nat × Nat) := [(9894168576,116732915178843,116733305230766)]
theorem point_links_checked75456 : (cuts75456.take 1).map (fun c => (9894100993-1+2*2^10*c.k,116732832336342+c.lower,116733222388215+c.upper)) = pointBounds75456 := by
 decide +kernel
def cuts75457 : List PrefixCut := [⟨64,163235730,163235830⟩]
theorem checked75457 : checkPrefixCuts (2^48) 9894232065 10 Manual.Count131072.C075457.packed 64 cuts75457 = true := by
 decide +kernel
def cuts75458 : List PrefixCut := [⟨56,140048720,140048805⟩,
⟨64,159933628,159933726⟩]
theorem checked75458 : checkPrefixCuts (2^48) 9894363137 10 Manual.Count131072.C075458.packed 64 cuts75458 = true := by
 decide +kernel
def pointBounds75458 : List (Nat × Nat × Nat) := [(9894477824,116733294989683,116733685041838)]
theorem point_links_checked75458 : (cuts75458.take 1).map (fun c => (9894363137-1+2*2^10*c.k,116733154940963+c.lower,116733544993033+c.upper)) = pointBounds75458 := by
 decide +kernel
def cuts75459 : List PrefixCut := [⟨64,162036619,162036718⟩]
theorem checked75459 : checkPrefixCuts (2^48) 9894494209 10 Manual.Count131072.C075459.packed 64 cuts75459 = true := by
 decide +kernel
def cuts75460 : List PrefixCut := [⟨64,161550873,161550966⟩]
theorem checked75460 : checkPrefixCuts (2^48) 9894625281 10 Manual.Count131072.C075460.packed 64 cuts75460 = true := by
 decide +kernel
def cuts75461 : List PrefixCut := [⟨15,38545455,38545478⟩,
⟨64,163796024,163796125⟩]
theorem checked75461 : checkPrefixCuts (2^48) 9894756353 10 Manual.Count131072.C075461.packed 64 cuts75461 = true := by
 decide +kernel
def pointBounds75461 : List (Nat × Nat × Nat) := [(9894787072,116733677007538,116734067059921)]
theorem point_links_checked75461 : (cuts75461.take 1).map (fun c => (9894756353-1+2*2^10*c.k,116733638462083+c.lower,116734028514443+c.upper)) = pointBounds75461 := by
 decide +kernel
def cuts75462 : List PrefixCut := [⟨64,160351857,160351954⟩]
theorem checked75462 : checkPrefixCuts (2^48) 9894887425 10 Manual.Count131072.C075462.packed 64 cuts75462 = true := by
 decide +kernel
def cuts75463 : List PrefixCut := [⟨38,95635485,95635541⟩,
⟨64,163108971,163109068⟩]
theorem checked75463 : checkPrefixCuts (2^48) 9895018497 10 Manual.Count131072.C075463.packed 64 cuts75463 = true := by
 decide +kernel
def pointBounds75463 : List (Nat × Nat × Nat) := [(9895096320,116734058245449,116734448298063)]
theorem point_links_checked75463 : (cuts75463.take 1).map (fun c => (9895018497-1+2*2^10*c.k,116733962609964+c.lower,116734352662522+c.upper)) = pointBounds75463 := by
 decide +kernel
def cuts75464 : List PrefixCut := [⟨64,163334384,163334475⟩]
theorem checked75464 : checkPrefixCuts (2^48) 9895149569 10 Manual.Count131072.C075464.packed 64 cuts75464 = true := by
 decide +kernel
def cuts75465 : List PrefixCut := [⟨61,156761424,156761521⟩,
⟨64,164185568,164185670⟩]
theorem checked75465 : checkPrefixCuts (2^48) 9895280641 10 Manual.Count131072.C075465.packed 64 cuts75465 = true := by
 decide +kernel
def pointBounds75465 : List (Nat × Nat × Nat) := [(9895405568,116734445814743,116734835867586)]
theorem point_links_checked75465 : (cuts75465.take 1).map (fun c => (9895280641-1+2*2^10*c.k,116734289053319+c.lower,116734679106065+c.upper)) = pointBounds75465 := by
 decide +kernel
def cuts75466 : List PrefixCut := [⟨64,161509588,161509690⟩]
theorem checked75466 : checkPrefixCuts (2^48) 9895411713 10 Manual.Count131072.C075466.packed 64 cuts75466 = true := by
 decide +kernel
def cuts75467 : List PrefixCut := [⟨64,162531446,162531542⟩]
theorem checked75467 : checkPrefixCuts (2^48) 9895542785 10 Manual.Count131072.C075467.packed 64 cuts75467 = true := by
 decide +kernel
def cuts75468 : List PrefixCut := [⟨20,49009321,49009350⟩,
⟨64,161220858,161220958⟩]
theorem checked75468 : checkPrefixCuts (2^48) 9895673857 10 Manual.Count131072.C075468.packed 64 cuts75468 = true := by
 decide +kernel
def pointBounds75468 : List (Nat × Nat × Nat) := [(9895714816,116734826289242,116735216342317)]
theorem point_links_checked75468 : (cuts75468.take 1).map (fun c => (9895673857-1+2*2^10*c.k,116734777279921+c.lower,116735167332967+c.upper)) = pointBounds75468 := by
 decide +kernel
def cuts75469 : List PrefixCut := [⟨64,162043590,162043689⟩]
theorem checked75469 : checkPrefixCuts (2^48) 9895804929 10 Manual.Count131072.C075469.packed 64 cuts75469 = true := by
 decide +kernel
def cuts75470 : List PrefixCut := [⟨43,109194055,109194120⟩,
⟨64,161586372,161586470⟩]
theorem checked75470 : checkPrefixCuts (2^48) 9895936001 10 Manual.Count131072.C075470.packed 64 cuts75470 = true := by
 decide +kernel
def pointBounds75470 : List (Nat × Nat × Nat) := [(9896024064,116735209738424,116735599791734)]
theorem point_links_checked75470 : (cuts75470.take 1).map (fun c => (9895936001-1+2*2^10*c.k,116735100544369+c.lower,116735490597614+c.upper)) = pointBounds75470 := by
 decide +kernel
def cuts75471 : List PrefixCut := [⟨64,162124638,162124737⟩]
theorem checked75471 : checkPrefixCuts (2^48) 9896067073 10 Manual.Count131072.C075471.packed 64 cuts75471 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000170
