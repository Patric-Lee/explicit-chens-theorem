import PlattAssemblyKernel
import PlattCertificates.Count131072.C061472
import PlattCertificates.Count131072.C061473
import PlattCertificates.Count131072.C061474
import PlattCertificates.Count131072.C061475
import PlattCertificates.Count131072.C061476
import PlattCertificates.Count131072.C061477
import PlattCertificates.Count131072.C061478
import PlattCertificates.Count131072.C061479
import PlattCertificates.Count131072.C061480
import PlattCertificates.Count131072.C061481
import PlattCertificates.Count131072.C061482
import PlattCertificates.Count131072.C061483
import PlattCertificates.Count131072.C061484
import PlattCertificates.Count131072.C061485
import PlattCertificates.Count131072.C061486
import PlattCertificates.Count131072.C061487
import PlattCertificates.Count131072.C061488
import PlattCertificates.Count131072.C061489
import PlattCertificates.Count131072.C061490
import PlattCertificates.Count131072.C061491
import PlattCertificates.Count131072.C061492
import PlattCertificates.Count131072.C061493
import PlattCertificates.Count131072.C061494
import PlattCertificates.Count131072.C061495
import PlattCertificates.Count131072.C061496
import PlattCertificates.Count131072.C061497
import PlattCertificates.Count131072.C061498
import PlattCertificates.Count131072.C061499
import PlattCertificates.Count131072.C061500
import PlattCertificates.Count131072.C061501
import PlattCertificates.Count131072.C061502
import PlattCertificates.Count131072.C061503
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000046
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61472 : List PrefixCut := [⟨44,137398767,137398840⟩,
⟨64,201087031,201087139⟩]
theorem checked61472 : checkPrefixCuts (2^48) 8061190145 10 Manual.Count131072.C061472.packed 64 cuts61472 = true := by
 decide +kernel
def pointBounds61472 : List (Nat × Nat × Nat) := [(8061280256,114216058613695,114216447192068)]
theorem point_links_checked61472 : (cuts61472.take 1).map (fun c => (8061190145-1+2*2^10*c.k,114215921214928+c.lower,114216309793228+c.upper)) = pointBounds61472 := by
 decide +kernel
def cuts61473 : List PrefixCut := [⟨64,196789039,196789152⟩]
theorem checked61473 : checkPrefixCuts (2^48) 8061321217 10 Manual.Count131072.C061473.packed 64 cuts61473 = true := by
 decide +kernel
def cuts61474 : List PrefixCut := [⟨40,125348347,125348423⟩,
⟨64,199683849,199683970⟩]
theorem checked61474 : checkPrefixCuts (2^48) 8061452289 10 Manual.Count131072.C061474.packed 64 cuts61474 = true := by
 decide +kernel
def pointBounds61474 : List (Nat × Nat × Nat) := [(8061534208,114216444439345,114216833017942)]
theorem point_links_checked61474 : (cuts61474.take 1).map (fun c => (8061452289-1+2*2^10*c.k,114216319090998+c.lower,114216707669519+c.upper)) = pointBounds61474 := by
 decide +kernel
def cuts61475 : List PrefixCut := [⟨64,198563312,198563426⟩]
theorem checked61475 : checkPrefixCuts (2^48) 8061583361 10 Manual.Count131072.C061475.packed 64 cuts61475 = true := by
 decide +kernel
def cuts61476 : List PrefixCut := [⟨36,112041779,112041843⟩,
⟨64,199642444,199642560⟩]
theorem checked61476 : checkPrefixCuts (2^48) 8061714433 10 Manual.Count131072.C061476.packed 64 cuts61476 = true := by
 decide +kernel
def pointBounds61476 : List (Nat × Nat × Nat) := [(8061788160,114216829379938,114217217958758)]
theorem point_links_checked61476 : (cuts61476.take 1).map (fun c => (8061714433-1+2*2^10*c.k,114216717338159+c.lower,114217105916915+c.upper)) = pointBounds61476 := by
 decide +kernel
def cuts61477 : List PrefixCut := [⟨64,203409930,203410048⟩]
theorem checked61477 : checkPrefixCuts (2^48) 8061845505 10 Manual.Count131072.C061477.packed 64 cuts61477 = true := by
 decide +kernel
def cuts61478 : List PrefixCut := [⟨32,100691218,100691280⟩,
⟨64,199601036,199601153⟩]
theorem checked61478 : checkPrefixCuts (2^48) 8061976577 10 Manual.Count131072.C061478.packed 64 cuts61478 = true := by
 decide +kernel
def pointBounds61478 : List (Nat × Nat × Nat) := [(8062042112,114217221081751,114217609660803)]
theorem point_links_checked61478 : (cuts61478.take 1).map (fun c => (8061976577-1+2*2^10*c.k,114217120390533+c.lower,114217508969523+c.upper)) = pointBounds61478 := by
 decide +kernel
def cuts61479 : List PrefixCut := [⟨64,201168867,201168985⟩]
theorem checked61479 : checkPrefixCuts (2^48) 8062107649 10 Manual.Count131072.C061479.packed 64 cuts61479 = true := by
 decide +kernel
def cuts61480 : List PrefixCut := [⟨28,86199262,86199311⟩,
⟨64,198407518,198407629⟩]
theorem checked61480 : checkPrefixCuts (2^48) 8062238721 10 Manual.Count131072.C061480.packed 64 cuts61480 = true := by
 decide +kernel
def pointBounds61480 : List (Nat × Nat × Nat) := [(8062296064,114217607359698,114217995938972)]
theorem point_links_checked61480 : (cuts61480.take 1).map (fun c => (8062238721-1+2*2^10*c.k,114217521160436+c.lower,114217909739661+c.upper)) = pointBounds61480 := by
 decide +kernel
def cuts61481 : List PrefixCut := [⟨64,201860563,201860676⟩]
theorem checked61481 : checkPrefixCuts (2^48) 8062369793 10 Manual.Count131072.C061481.packed 64 cuts61481 = true := by
 decide +kernel
def cuts61482 : List PrefixCut := [⟨24,74955003,74955042⟩,
⟨64,200670313,200670426⟩]
theorem checked61482 : checkPrefixCuts (2^48) 8062500865 10 Manual.Count131072.C061482.packed 64 cuts61482 = true := by
 decide +kernel
def pointBounds61482 : List (Nat × Nat × Nat) := [(8062550016,114217996383520,114218384963008)]
theorem point_links_checked61482 : (cuts61482.take 1).map (fun c => (8062500865-1+2*2^10*c.k,114217921428517+c.lower,114218310007966+c.upper)) = pointBounds61482 := by
 decide +kernel
def cuts61483 : List PrefixCut := [⟨64,200981245,200981357⟩]
theorem checked61483 : checkPrefixCuts (2^48) 8062631937 10 Manual.Count131072.C061483.packed 64 cuts61483 = true := by
 decide +kernel
def cuts61484 : List PrefixCut := [⟨20,62349954,62349988⟩,
⟨64,200768511,200768626⟩]
theorem checked61484 : checkPrefixCuts (2^48) 8062763009 10 Manual.Count131072.C061484.packed 64 cuts61484 = true := by
 decide +kernel
def pointBounds61484 : List (Nat × Nat × Nat) := [(8062803968,114218385430029,114218774009737)]
theorem point_links_checked61484 : (cuts61484.take 1).map (fun c => (8062763009-1+2*2^10*c.k,114218323080075+c.lower,114218711659749+c.upper)) = pointBounds61484 := by
 decide +kernel
def cuts61485 : List PrefixCut := [⟨64,200835086,200835202⟩]
theorem checked61485 : checkPrefixCuts (2^48) 8062894081 10 Manual.Count131072.C061485.packed 64 cuts61485 = true := by
 decide +kernel
def cuts61486 : List PrefixCut := [⟨16,50234440,50234472⟩,
⟨64,199540164,199540282⟩]
theorem checked61486 : checkPrefixCuts (2^48) 8063025153 10 Manual.Count131072.C061486.packed 64 cuts61486 = true := by
 decide +kernel
def pointBounds61486 : List (Nat × Nat × Nat) := [(8063057920,114218774918112,114219163498049)]
theorem point_links_checked61486 : (cuts61486.take 1).map (fun c => (8063025153-1+2*2^10*c.k,114218724683672+c.lower,114219113263577+c.upper)) = pointBounds61486 := by
 decide +kernel
def cuts61487 : List PrefixCut := [⟨64,201352166,201352287⟩]
theorem checked61487 : checkPrefixCuts (2^48) 8063156225 10 Manual.Count131072.C061487.packed 64 cuts61487 = true := by
 decide +kernel
def cuts61488 : List PrefixCut := [⟨12,36967733,36967754⟩,
⟨64,200999812,200999925⟩]
theorem checked61488 : checkPrefixCuts (2^48) 8063287297 10 Manual.Count131072.C061488.packed 64 cuts61488 = true := by
 decide +kernel
def pointBounds61488 : List (Nat × Nat × Nat) := [(8063311872,114219162543735,114219551123900)]
theorem point_links_checked61488 : (cuts61488.take 1).map (fun c => (8063287297-1+2*2^10*c.k,114219125576002+c.lower,114219514156146+c.upper)) = pointBounds61488 := by
 decide +kernel
def cuts61489 : List PrefixCut := [⟨64,200263512,200263624⟩]
theorem checked61489 : checkPrefixCuts (2^48) 8063418369 10 Manual.Count131072.C061489.packed 64 cuts61489 = true := by
 decide +kernel
def cuts61490 : List PrefixCut := [⟨8,25482135,25482151⟩,
⟨64,201970680,201970795⟩]
theorem checked61490 : checkPrefixCuts (2^48) 8063549441 10 Manual.Count131072.C061490.packed 64 cuts61490 = true := by
 decide +kernel
def pointBounds61490 : List (Nat × Nat × Nat) := [(8063565824,114219552321461,114219940901846)]
theorem point_links_checked61490 : (cuts61490.take 1).map (fun c => (8063549441-1+2*2^10*c.k,114219526839326+c.lower,114219915419695+c.upper)) = pointBounds61490 := by
 decide +kernel
def cuts61491 : List PrefixCut := [⟨64,202002289,202002408⟩]
theorem checked61491 : checkPrefixCuts (2^48) 8063680513 10 Manual.Count131072.C061491.packed 64 cuts61491 = true := by
 decide +kernel
def cuts61492 : List PrefixCut := [⟨4,13089720,13089727⟩,
⟨64,198648087,198648199⟩]
theorem checked61492 : checkPrefixCuts (2^48) 8063811585 10 Manual.Count131072.C061492.packed 64 cuts61492 = true := by
 decide +kernel
def pointBounds61492 : List (Nat × Nat × Nat) := [(8063819776,114219943902015,114220332482625)]
theorem point_links_checked61492 : (cuts61492.take 1).map (fun c => (8063811585-1+2*2^10*c.k,114219930812295+c.lower,114220319392898+c.upper)) = pointBounds61492 := by
 decide +kernel
def cuts61493 : List PrefixCut := [⟨64,202693836,202693953⟩]
theorem checked61493 : checkPrefixCuts (2^48) 8063942657 10 Manual.Count131072.C061493.packed 64 cuts61493 = true := by
 decide +kernel
def pointBounds61493 : List (Nat × Nat × Nat) := [(8064073728,114220332154218,114220720735050)]
theorem point_links_checked61493 : (cuts61493.take 1).map (fun c => (8063942657-1+2*2^10*c.k,114220129460382+c.lower,114220518041097+c.upper)) = pointBounds61493 := by
 decide +kernel
def cuts61494 : List PrefixCut := [⟨64,200142500,200142618⟩]
theorem checked61494 : checkPrefixCuts (2^48) 8064073729 10 Manual.Count131072.C061494.packed 64 cuts61494 = true := by
 decide +kernel
def cuts61495 : List PrefixCut := [⟨60,188272008,188272119⟩,
⟨64,201151468,201151586⟩]
theorem checked61495 : checkPrefixCuts (2^48) 8064204801 10 Manual.Count131072.C061495.packed 64 cuts61495 = true := by
 decide +kernel
def pointBounds61495 : List (Nat × Nat × Nat) := [(8064327680,114220720568726,114221109149787)]
theorem point_links_checked61495 : (cuts61495.take 1).map (fun c => (8064204801-1+2*2^10*c.k,114220532296718+c.lower,114220920877668+c.upper)) = pointBounds61495 := by
 decide +kernel
def cuts61496 : List PrefixCut := [⟨64,200310518,200310632⟩]
theorem checked61496 : checkPrefixCuts (2^48) 8064335873 10 Manual.Count131072.C061496.packed 64 cuts61496 = true := by
 decide +kernel
def cuts61497 : List PrefixCut := [⟨56,174514263,174514362⟩,
⟨64,200237457,200237570⟩]
theorem checked61497 : checkPrefixCuts (2^48) 8064466945 10 Manual.Count131072.C061497.packed 64 cuts61497 = true := by
 decide +kernel
def pointBounds61497 : List (Nat × Nat × Nat) := [(8064581632,114221108272967,114221496854248)]
theorem point_links_checked61497 : (cuts61497.take 1).map (fun c => (8064466945-1+2*2^10*c.k,114220933758704+c.lower,114221322339886+c.upper)) = pointBounds61497 := by
 decide +kernel
def cuts61498 : List PrefixCut := [⟨64,200408718,200408833⟩]
theorem checked61498 : checkPrefixCuts (2^48) 8064598017 10 Manual.Count131072.C061498.packed 64 cuts61498 = true := by
 decide +kernel
def cuts61499 : List PrefixCut := [⟨52,162467580,162467677⟩,
⟨64,198625484,198625601⟩]
theorem checked61499 : checkPrefixCuts (2^48) 8064729089 10 Manual.Count131072.C061499.packed 64 cuts61499 = true := by
 decide +kernel
def pointBounds61499 : List (Nat × Nat × Nat) := [(8064835584,114221496872459,114221885453966)]
theorem point_links_checked61499 : (cuts61499.take 1).map (fun c => (8064729089-1+2*2^10*c.k,114221334404879+c.lower,114221722986289+c.upper)) = pointBounds61499 := by
 decide +kernel
def cuts61500 : List PrefixCut := [⟨64,202915075,202915192⟩]
theorem checked61500 : checkPrefixCuts (2^48) 8064860161 10 Manual.Count131072.C061500.packed 64 cuts61500 = true := by
 decide +kernel
def cuts61501 : List PrefixCut := [⟨48,149584052,149584140⟩,
⟨64,201376147,201376264⟩]
theorem checked61501 : checkPrefixCuts (2^48) 8064991233 10 Manual.Count131072.C061501.packed 64 cuts61501 = true := by
 decide +kernel
def pointBounds61501 : List (Nat × Nat × Nat) := [(8065089536,114221885529490,114222274111222)]
theorem point_links_checked61501 : (cuts61501.take 1).map (fun c => (8064991233-1+2*2^10*c.k,114221735945438+c.lower,114222124527082+c.upper)) = pointBounds61501 := by
 decide +kernel
def cuts61502 : List PrefixCut := [⟨64,199802393,199802509⟩]
theorem checked61502 : checkPrefixCuts (2^48) 8065122305 10 Manual.Count131072.C061502.packed 64 cuts61502 = true := by
 decide +kernel
def cuts61503 : List PrefixCut := [⟨44,139702698,139702776⟩,
⟨64,201334716,201334830⟩]
theorem checked61503 : checkPrefixCuts (2^48) 8065253377 10 Manual.Count131072.C061503.packed 64 cuts61503 = true := by
 decide +kernel
def pointBounds61503 : List (Nat × Nat × Nat) := [(8065343488,114222276826676,114222665408631)]
theorem point_links_checked61503 : (cuts61503.take 1).map (fun c => (8065253377-1+2*2^10*c.k,114222137123978+c.lower,114222525705855+c.upper)) = pointBounds61503 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000046
