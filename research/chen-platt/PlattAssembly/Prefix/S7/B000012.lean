import PlattAssemblyKernel
import PlattCertificates.Count131072.C060384
import PlattCertificates.Count131072.C060385
import PlattCertificates.Count131072.C060386
import PlattCertificates.Count131072.C060387
import PlattCertificates.Count131072.C060388
import PlattCertificates.Count131072.C060389
import PlattCertificates.Count131072.C060390
import PlattCertificates.Count131072.C060391
import PlattCertificates.Count131072.C060392
import PlattCertificates.Count131072.C060393
import PlattCertificates.Count131072.C060394
import PlattCertificates.Count131072.C060395
import PlattCertificates.Count131072.C060396
import PlattCertificates.Count131072.C060397
import PlattCertificates.Count131072.C060398
import PlattCertificates.Count131072.C060399
import PlattCertificates.Count131072.C060400
import PlattCertificates.Count131072.C060401
import PlattCertificates.Count131072.C060402
import PlattCertificates.Count131072.C060403
import PlattCertificates.Count131072.C060404
import PlattCertificates.Count131072.C060405
import PlattCertificates.Count131072.C060406
import PlattCertificates.Count131072.C060407
import PlattCertificates.Count131072.C060408
import PlattCertificates.Count131072.C060409
import PlattCertificates.Count131072.C060410
import PlattCertificates.Count131072.C060411
import PlattCertificates.Count131072.C060412
import PlattCertificates.Count131072.C060413
import PlattCertificates.Count131072.C060414
import PlattCertificates.Count131072.C060415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60384 : List PrefixCut := [⟨42,132621830,132621907⟩,
⟨64,202682264,202682380⟩]
theorem checked60384 : checkPrefixCuts (2^48) 7918583809 10 Manual.Count131072.C060384.packed 64 cuts60384 = true := by
 decide +kernel
def pointBounds60384 : List (Nat × Nat × Nat) := [(7918669824,113995680374308,113996068826582)]
theorem point_links_checked60384 : (cuts60384.take 1).map (fun c => (7918583809-1+2*2^10*c.k,113995547752478+c.lower,113995936204675+c.upper)) = pointBounds60384 := by
 decide +kernel
def cuts60385 : List PrefixCut := [⟨64,205558087,205558204⟩]
theorem checked60385 : checkPrefixCuts (2^48) 7918714881 10 Manual.Count131072.C060385.packed 64 cuts60385 = true := by
 decide +kernel
def cuts60386 : List PrefixCut := [⟨35,111503967,111504029⟩,
⟨64,204061802,204061916⟩]
theorem checked60386 : checkPrefixCuts (2^48) 7918845953 10 Manual.Count131072.C060386.packed 64 cuts60386 = true := by
 decide +kernel
def pointBounds60386 : List (Nat × Nat × Nat) := [(7918917632,113996067496796,113996455949288)]
theorem point_links_checked60386 : (cuts60386.take 1).map (fun c => (7918845953-1+2*2^10*c.k,113995955992829+c.lower,113996344445259+c.upper)) = pointBounds60386 := by
 decide +kernel
def cuts60387 : List PrefixCut := [⟨64,205657907,205658025⟩]
theorem checked60387 : checkPrefixCuts (2^48) 7918977025 10 Manual.Count131072.C060387.packed 64 cuts60387 = true := by
 decide +kernel
def cuts60388 : List PrefixCut := [⟨28,89463327,89463379⟩,
⟨64,205050265,205050381⟩]
theorem checked60388 : checkPrefixCuts (2^48) 7919108097 10 Manual.Count131072.C060388.packed 64 cuts60388 = true := by
 decide +kernel
def pointBounds60388 : List (Nat × Nat × Nat) := [(7919165440,113996455175865,113996843628579)]
theorem point_links_checked60388 : (cuts60388.take 1).map (fun c => (7919108097-1+2*2^10*c.k,113996365712538+c.lower,113996754165200+c.upper)) = pointBounds60388 := by
 decide +kernel
def cuts60389 : List PrefixCut := [⟨64,205117976,205118090⟩]
theorem checked60389 : checkPrefixCuts (2^48) 7919239169 10 Manual.Count131072.C060389.packed 64 cuts60389 = true := by
 decide +kernel
def cuts60390 : List PrefixCut := [⟨21,66784337,66784377⟩,
⟨64,204012745,204012863⟩]
theorem checked60390 : checkPrefixCuts (2^48) 7919370241 10 Manual.Count131072.C060390.packed 64 cuts60390 = true := by
 decide +kernel
def pointBounds60390 : List (Nat × Nat × Nat) := [(7919413248,113996842665116,113997231118048)]
theorem point_links_checked60390 : (cuts60390.take 1).map (fun c => (7919370241-1+2*2^10*c.k,113996775880779+c.lower,113997164333671+c.upper)) = pointBounds60390 := by
 decide +kernel
def cuts60391 : List PrefixCut := [⟨64,202445546,202445661⟩]
theorem checked60391 : checkPrefixCuts (2^48) 7919501313 10 Manual.Count131072.C060391.packed 64 cuts60391 = true := by
 decide +kernel
def cuts60392 : List PrefixCut := [⟨14,44817632,44817660⟩,
⟨64,204148162,204148282⟩]
theorem checked60392 : checkPrefixCuts (2^48) 7919632385 10 Manual.Count131072.C060392.packed 64 cuts60392 = true := by
 decide +kernel
def pointBounds60392 : List (Nat × Nat × Nat) := [(7919661056,113997227156702,113997615609855)]
theorem point_links_checked60392 : (cuts60392.take 1).map (fun c => (7919632385-1+2*2^10*c.k,113997182339070+c.lower,113997570792195+c.upper)) = pointBounds60392 := by
 decide +kernel
def cuts60393 : List PrefixCut := [⟨64,203256275,203256391⟩]
theorem checked60393 : checkPrefixCuts (2^48) 7919763457 10 Manual.Count131072.C060393.packed 64 cuts60393 = true := by
 decide +kernel
def cuts60394 : List PrefixCut := [⟨7,22994511,22994524⟩,
⟨64,203324003,203324124⟩]
theorem checked60394 : checkPrefixCuts (2^48) 7919894529 10 Manual.Count131072.C060394.packed 64 cuts60394 = true := by
 decide +kernel
def pointBounds60394 : List (Nat × Nat × Nat) := [(7919908864,113997612738018,113998001191392)]
theorem point_links_checked60394 : (cuts60394.take 1).map (fun c => (7919894529-1+2*2^10*c.k,113997589743507+c.lower,113997978196868+c.upper)) = pointBounds60394 := by
 decide +kernel
def cuts60395 : List PrefixCut := [⟨64,205097585,205097701⟩]
theorem checked60395 : checkPrefixCuts (2^48) 7920025601 10 Manual.Count131072.C060395.packed 64 cuts60395 = true := by
 decide +kernel
def pointBounds60395 : List (Nat × Nat × Nat) := [(7920156672,113997998165095,113998386618693)]
theorem point_links_checked60395 : (cuts60395.take 1).map (fun c => (7920025601-1+2*2^10*c.k,113997793067510+c.lower,113998181520992+c.upper)) = pointBounds60395 := by
 decide +kernel
def cuts60396 : List PrefixCut := [⟨64,205342965,205343081⟩]
theorem checked60396 : checkPrefixCuts (2^48) 7920156673 10 Manual.Count131072.C060396.packed 64 cuts60396 = true := by
 decide +kernel
def cuts60397 : List PrefixCut := [⟨57,181920070,181920174⟩,
⟨64,203669273,203669389⟩]
theorem checked60397 : checkPrefixCuts (2^48) 7920287745 10 Manual.Count131072.C060397.packed 64 cuts60397 = true := by
 decide +kernel
def pointBounds60397 : List (Nat × Nat × Nat) := [(7920404480,113998385428130,113998773881948)]
theorem point_links_checked60397 : (cuts60397.take 1).map (fun c => (7920287745-1+2*2^10*c.k,113998203508060+c.lower,113998591961774+c.upper)) = pointBounds60397 := by
 decide +kernel
def cuts60398 : List PrefixCut := [⟨64,205798156,205798277⟩]
theorem checked60398 : checkPrefixCuts (2^48) 7920418817 10 Manual.Count131072.C060398.packed 64 cuts60398 = true := by
 decide +kernel
def cuts60399 : List PrefixCut := [⟨50,161231666,161231757⟩,
⟨64,206221217,206221332⟩]
theorem checked60399 : checkPrefixCuts (2^48) 7920549889 10 Manual.Count131072.C060399.packed 64 cuts60399 = true := by
 decide +kernel
def pointBounds60399 : List (Nat × Nat × Nat) := [(7920652288,113998774207155,113999162661197)]
theorem point_links_checked60399 : (cuts60399.take 1).map (fun c => (7920549889-1+2*2^10*c.k,113998612975489+c.lower,113999001429440+c.upper)) = pointBounds60399 := by
 decide +kernel
def cuts60400 : List PrefixCut := [⟨64,203161663,203161780⟩]
theorem checked60400 : checkPrefixCuts (2^48) 7920680961 10 Manual.Count131072.C060400.packed 64 cuts60400 = true := by
 decide +kernel
def cuts60401 : List PrefixCut := [⟨43,139123117,139123196⟩,
⟨64,205503668,205503778⟩]
theorem checked60401 : checkPrefixCuts (2^48) 7920812033 10 Manual.Count131072.C060401.packed 64 cuts60401 = true := by
 decide +kernel
def pointBounds60401 : List (Nat × Nat × Nat) := [(7920900096,113999161481486,113999549935748)]
theorem point_links_checked60401 : (cuts60401.take 1).map (fun c => (7920812033-1+2*2^10*c.k,113999022358369+c.lower,113999410812552+c.upper)) = pointBounds60401 := by
 decide +kernel
def cuts60402 : List PrefixCut := [⟨64,205393668,205393789⟩]
theorem checked60402 : checkPrefixCuts (2^48) 7920943105 10 Manual.Count131072.C060402.packed 64 cuts60402 = true := by
 decide +kernel
def cuts60403 : List PrefixCut := [⟨36,113569143,113569205⟩,
⟨64,204253141,204253255⟩]
theorem checked60403 : checkPrefixCuts (2^48) 7921074177 10 Manual.Count131072.C060403.packed 64 cuts60403 = true := by
 decide +kernel
def pointBounds60403 : List (Nat × Nat × Nat) := [(7921147904,113999546824848,113999935279324)]
theorem point_links_checked60403 : (cuts60403.take 1).map (fun c => (7921074177-1+2*2^10*c.k,113999433255705+c.lower,113999821710119+c.upper)) = pointBounds60403 := by
 decide +kernel
def cuts60404 : List PrefixCut := [⟨64,203041623,203041743⟩]
theorem checked60404 : checkPrefixCuts (2^48) 7921205249 10 Manual.Count131072.C060404.packed 64 cuts60404 = true := by
 decide +kernel
def cuts60405 : List PrefixCut := [⟨29,94839269,94839320⟩,
⟨64,207586547,207586659⟩]
theorem checked60405 : checkPrefixCuts (2^48) 7921336321 10 Manual.Count131072.C060405.packed 64 cuts60405 = true := by
 decide +kernel
def pointBounds60405 : List (Nat × Nat × Nat) := [(7921395712,113999935389738,114000323844437)]
theorem point_links_checked60405 : (cuts60405.take 1).map (fun c => (7921336321-1+2*2^10*c.k,113999840550469+c.lower,114000229005117+c.upper)) = pointBounds60405 := by
 decide +kernel
def cuts60406 : List PrefixCut := [⟨64,202999355,202999473⟩]
theorem checked60406 : checkPrefixCuts (2^48) 7921467393 10 Manual.Count131072.C060406.packed 64 cuts60406 = true := by
 decide +kernel
def cuts60407 : List PrefixCut := [⟨22,69323884,69323925⟩,
⟨64,206264952,206265074⟩]
theorem checked60407 : checkPrefixCuts (2^48) 7921598465 10 Manual.Count131072.C060407.packed 64 cuts60407 = true := by
 decide +kernel
def pointBounds60407 : List (Nat × Nat × Nat) := [(7921643520,114000320460255,114000708915174)]
theorem point_links_checked60407 : (cuts60407.take 1).map (fun c => (7921598465-1+2*2^10*c.k,114000251136371+c.lower,114000639591249+c.upper)) = pointBounds60407 := by
 decide +kernel
def cuts60408 : List PrefixCut := [⟨64,203099254,203099367⟩]
theorem checked60408 : checkPrefixCuts (2^48) 7921729537 10 Manual.Count131072.C060408.packed 64 cuts60408 = true := by
 decide +kernel
def cuts60409 : List PrefixCut := [⟨15,47540938,47540965⟩,
⟨64,204801366,204801482⟩]
theorem checked60409 : checkPrefixCuts (2^48) 7921860609 10 Manual.Count131072.C060409.packed 64 cuts60409 = true := by
 decide +kernel
def pointBounds60409 : List (Nat × Nat × Nat) := [(7921891328,114000708041515,114001096496655)]
theorem point_links_checked60409 : (cuts60409.take 1).map (fun c => (7921860609-1+2*2^10*c.k,114000660500577+c.lower,114001048955690+c.upper)) = pointBounds60409 := by
 decide +kernel
def cuts60410 : List PrefixCut := [⟨64,204087373,204087491⟩]
theorem checked60410 : checkPrefixCuts (2^48) 7921991681 10 Manual.Count131072.C060410.packed 64 cuts60410 = true := by
 decide +kernel
def cuts60411 : List PrefixCut := [⟨8,25084321,25084335⟩,
⟨64,206286844,206286963⟩]
theorem checked60411 : checkPrefixCuts (2^48) 7922122753 10 Manual.Count131072.C060411.packed 64 cuts60411 = true := by
 decide +kernel
def pointBounds60411 : List (Nat × Nat × Nat) := [(7922139136,114001094473637,114001482928998)]
theorem point_links_checked60411 : (cuts60411.take 1).map (fun c => (7922122753-1+2*2^10*c.k,114001069389316+c.lower,114001457844663+c.upper)) = pointBounds60411 := by
 decide +kernel
def cuts60412 : List PrefixCut := [⟨64,203014724,203014842⟩]
theorem checked60412 : checkPrefixCuts (2^48) 7922253825 10 Manual.Count131072.C060412.packed 64 cuts60412 = true := by
 decide +kernel
def cuts60413 : List PrefixCut := [⟨1,3197615,3197617⟩,
⟨64,202656083,202656203⟩]
theorem checked60413 : checkPrefixCuts (2^48) 7922384897 10 Manual.Count131072.C060413.packed 64 cuts60413 = true := by
 decide +kernel
def pointBounds60413 : List (Nat × Nat × Nat) := [(7922386944,114001481888499,114001870344085)]
theorem point_links_checked60413 : (cuts60413.take 1).map (fun c => (7922384897-1+2*2^10*c.k,114001478690884+c.lower,114001867146468+c.upper)) = pointBounds60413 := by
 decide +kernel
def cuts60414 : List PrefixCut := [⟨58,186842842,186842951⟩,
⟨64,205352884,205353004⟩]
theorem checked60414 : checkPrefixCuts (2^48) 7922515969 10 Manual.Count131072.C060414.packed 64 cuts60414 = true := by
 decide +kernel
def pointBounds60414 : List (Nat × Nat × Nat) := [(7922634752,114001868189809,114002256645622)]
theorem point_links_checked60414 : (cuts60414.take 1).map (fun c => (7922515969-1+2*2^10*c.k,114001681346967+c.lower,114002069802671+c.upper)) = pointBounds60414 := by
 decide +kernel
def cuts60415 : List PrefixCut := [⟨64,206486354,206486468⟩]
theorem checked60415 : checkPrefixCuts (2^48) 7922647041 10 Manual.Count131072.C060415.packed 64 cuts60415 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000012
