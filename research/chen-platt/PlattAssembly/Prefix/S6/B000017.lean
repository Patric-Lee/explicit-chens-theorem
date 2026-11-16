import PlattAssemblyKernel
import PlattCertificates.Count131072.C050544
import PlattCertificates.Count131072.C050545
import PlattCertificates.Count131072.C050546
import PlattCertificates.Count131072.C050547
import PlattCertificates.Count131072.C050548
import PlattCertificates.Count131072.C050549
import PlattCertificates.Count131072.C050550
import PlattCertificates.Count131072.C050551
import PlattCertificates.Count131072.C050552
import PlattCertificates.Count131072.C050553
import PlattCertificates.Count131072.C050554
import PlattCertificates.Count131072.C050555
import PlattCertificates.Count131072.C050556
import PlattCertificates.Count131072.C050557
import PlattCertificates.Count131072.C050558
import PlattCertificates.Count131072.C050559
import PlattCertificates.Count131072.C050560
import PlattCertificates.Count131072.C050561
import PlattCertificates.Count131072.C050562
import PlattCertificates.Count131072.C050563
import PlattCertificates.Count131072.C050564
import PlattCertificates.Count131072.C050565
import PlattCertificates.Count131072.C050566
import PlattCertificates.Count131072.C050567
import PlattCertificates.Count131072.C050568
import PlattCertificates.Count131072.C050569
import PlattCertificates.Count131072.C050570
import PlattCertificates.Count131072.C050571
import PlattCertificates.Count131072.C050572
import PlattCertificates.Count131072.C050573
import PlattCertificates.Count131072.C050574
import PlattCertificates.Count131072.C050575
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50544 : List PrefixCut := [⟨64,244070286,244070425⟩]
theorem checked50544 : checkPrefixCuts (2^48) 6628835329 10 Manual.Count131072.C050544.packed 64 cuts50544 = true := by
 decide +kernel
def cuts50545 : List PrefixCut := [⟨24,90782044,90782094⟩,
⟨64,247037701,247037838⟩]
theorem checked50545 : checkPrefixCuts (2^48) 6628966401 10 Manual.Count131072.C050545.packed 64 cuts50545 = true := by
 decide +kernel
def pointBounds50545 : List (Nat × Nat × Nat) := [(6629015552,111791860182307,111792247381162)]
theorem point_links_checked50545 : (cuts50545.take 1).map (fun c => (6628966401-1+2*2^10*c.k,111791769400263+c.lower,111792156599068+c.upper)) = pointBounds50545 := by
 decide +kernel
def cuts50546 : List PrefixCut := [⟨62,238625843,238625971⟩,
⟨64,246947942,246948075⟩]
theorem checked50546 : checkPrefixCuts (2^48) 6629097473 10 Manual.Count131072.C050546.packed 64 cuts50546 = true := by
 decide +kernel
def pointBounds50546 : List (Nat × Nat × Nat) := [(6629224448,111792255063807,111792642262877)]
theorem point_links_checked50546 : (cuts50546.take 1).map (fun c => (6629097473-1+2*2^10*c.k,111792016437964+c.lower,111792403636906+c.upper)) = pointBounds50546 := by
 decide +kernel
def cuts50547 : List PrefixCut := [⟨64,245287100,245287243⟩]
theorem checked50547 : checkPrefixCuts (2^48) 6629228545 10 Manual.Count131072.C050547.packed 64 cuts50547 = true := by
 decide +kernel
def cuts50548 : List PrefixCut := [⟨36,139434041,139434119⟩,
⟨64,248848772,248848915⟩]
theorem checked50548 : checkPrefixCuts (2^48) 6629359617 10 Manual.Count131072.C050548.packed 64 cuts50548 = true := by
 decide +kernel
def pointBounds50548 : List (Nat × Nat × Nat) := [(6629433344,111792648107047,111793035306343)]
theorem point_links_checked50548 : (cuts50548.take 1).map (fun c => (6629359617-1+2*2^10*c.k,111792508673006+c.lower,111792895872224+c.upper)) = pointBounds50548 := by
 decide +kernel
def cuts50549 : List PrefixCut := [⟨64,240309869,240310005⟩]
theorem checked50549 : checkPrefixCuts (2^48) 6629490689 10 Manual.Count131072.C050549.packed 64 cuts50549 = true := by
 decide +kernel
def cuts50550 : List PrefixCut := [⟨10,38933155,38933176⟩,
⟨64,247862434,247862572⟩]
theorem checked50550 : checkPrefixCuts (2^48) 6629621761 10 Manual.Count131072.C050550.packed 64 cuts50550 = true := by
 decide +kernel
def pointBounds50550 : List (Nat × Nat × Nat) := [(6629642240,111793036764802,111793423964320)]
theorem point_links_checked50550 : (cuts50550.take 1).map (fun c => (6629621761-1+2*2^10*c.k,111792997831647+c.lower,111793385031144+c.upper)) = pointBounds50550 := by
 decide +kernel
def cuts50551 : List PrefixCut := [⟨48,183919412,183919517⟩,
⟨64,242847766,242847904⟩]
theorem checked50551 : checkPrefixCuts (2^48) 6629752833 10 Manual.Count131072.C050551.packed 64 cuts50551 = true := by
 decide +kernel
def pointBounds50551 : List (Nat × Nat × Nat) := [(6629851136,111793429613493,111793816813233)]
theorem point_links_checked50551 : (cuts50551.take 1).map (fun c => (6629752833-1+2*2^10*c.k,111793245694081+c.lower,111793632893716+c.upper)) = pointBounds50551 := by
 decide +kernel
def cuts50552 : List PrefixCut := [⟨64,246196894,246197032⟩]
theorem checked50552 : checkPrefixCuts (2^48) 6629883905 10 Manual.Count131072.C050552.packed 64 cuts50552 = true := by
 decide +kernel
def cuts50553 : List PrefixCut := [⟨22,83720265,83720314⟩,
⟨64,244536303,244536442⟩]
theorem checked50553 : checkPrefixCuts (2^48) 6630014977 10 Manual.Count131072.C050553.packed 64 cuts50553 = true := by
 decide +kernel
def pointBounds50553 : List (Nat × Nat × Nat) := [(6630060032,111793818459006,111794205658966)]
theorem point_links_checked50553 : (cuts50553.take 1).map (fun c => (6630014977-1+2*2^10*c.k,111793734738741+c.lower,111794121938652+c.upper)) = pointBounds50553 := by
 decide +kernel
def cuts50554 : List PrefixCut := [⟨60,233154091,233154223⟩,
⟨64,248309807,248309948⟩]
theorem checked50554 : checkPrefixCuts (2^48) 6630146049 10 Manual.Count131072.C050554.packed 64 cuts50554 = true := by
 decide +kernel
def pointBounds50554 : List (Nat × Nat × Nat) := [(6630268928,111794212429135,111794599629317)]
theorem point_links_checked50554 : (cuts50554.take 1).map (fun c => (6630146049-1+2*2^10*c.k,111793979275044+c.lower,111794366475094+c.upper)) = pointBounds50554 := by
 decide +kernel
def cuts50555 : List PrefixCut := [⟨64,240451199,240451334⟩]
theorem checked50555 : checkPrefixCuts (2^48) 6630277121 10 Manual.Count131072.C050555.packed 64 cuts50555 = true := by
 decide +kernel
def cuts50556 : List PrefixCut := [⟨34,132492380,132492454⟩,
⟨64,247323645,247323781⟩]
theorem checked50556 : checkPrefixCuts (2^48) 6630408193 10 Manual.Count131072.C050556.packed 64 cuts50556 = true := by
 decide +kernel
def pointBounds50556 : List (Nat × Nat × Nat) := [(6630477824,111794600528430,111794987728830)]
theorem point_links_checked50556 : (cuts50556.take 1).map (fun c => (6630408193-1+2*2^10*c.k,111794468036050+c.lower,111794855236376+c.upper)) = pointBounds50556 := by
 decide +kernel
def cuts50557 : List PrefixCut := [⟨64,246597063,246597205⟩]
theorem checked50557 : checkPrefixCuts (2^48) 6630539265 10 Manual.Count131072.C050557.packed 64 cuts50557 = true := by
 decide +kernel
def cuts50558 : List PrefixCut := [⟨8,30054878,30054895⟩,
⟨64,247568543,247568687⟩]
theorem checked50558 : checkPrefixCuts (2^48) 6630670337 10 Manual.Count131072.C050558.packed 64 cuts50558 = true := by
 decide +kernel
def pointBounds50558 : List (Nat × Nat × Nat) := [(6630686720,111794992011636,111795379212257)]
theorem point_links_checked50558 : (cuts50558.take 1).map (fun c => (6630670337-1+2*2^10*c.k,111794961956758+c.lower,111795349157362+c.upper)) = pointBounds50558 := by
 decide +kernel
def cuts50559 : List PrefixCut := [⟨46,181895262,181895364⟩,
⟨64,251086942,251087084⟩]
theorem checked50559 : checkPrefixCuts (2^48) 6630801409 10 Manual.Count131072.C050559.packed 64 cuts50559 = true := by
 decide +kernel
def pointBounds50559 : List (Nat × Nat × Nat) := [(6630895616,111795391420563,111795778621413)]
theorem point_links_checked50559 : (cuts50559.take 1).map (fun c => (6630801409-1+2*2^10*c.k,111795209525301+c.lower,111795596726049+c.upper)) = pointBounds50559 := by
 decide +kernel
def cuts50560 : List PrefixCut := [⟨64,249850955,249851095⟩]
theorem checked50560 : checkPrefixCuts (2^48) 6630932481 10 Manual.Count131072.C050560.packed 64 cuts50560 = true := by
 decide +kernel
def cuts50561 : List PrefixCut := [⟨20,77721911,77721956⟩,
⟨64,246874702,246874840⟩]
theorem checked50561 : checkPrefixCuts (2^48) 6631063553 10 Manual.Count131072.C050561.packed 64 cuts50561 = true := by
 decide +kernel
def pointBounds50561 : List (Nat × Nat × Nat) := [(6631104512,111795788185109,111796175386184)]
theorem point_links_checked50561 : (cuts50561.take 1).map (fun c => (6631063553-1+2*2^10*c.k,111795710463198+c.lower,111796097664228+c.upper)) = pointBounds50561 := by
 decide +kernel
def cuts50562 : List PrefixCut := [⟨58,225434478,225434609⟩,
⟨64,248355473,248355618⟩]
theorem checked50562 : checkPrefixCuts (2^48) 6631194625 10 Manual.Count131072.C050562.packed 64 cuts50562 = true := by
 decide +kernel
def pointBounds50562 : List (Nat × Nat × Nat) := [(6631313408,111796182772378,111796569973677)]
theorem point_links_checked50562 : (cuts50562.take 1).map (fun c => (6631194625-1+2*2^10*c.k,111795957337900+c.lower,111796344539068+c.upper)) = pointBounds50562 := by
 decide +kernel
def cuts50563 : List PrefixCut := [⟨64,239691599,239691736⟩]
theorem checked50563 : checkPrefixCuts (2^48) 6631325697 10 Manual.Count131072.C050563.packed 64 cuts50563 = true := by
 decide +kernel
def cuts50564 : List PrefixCut := [⟨32,122496845,122496911⟩,
⟨64,244822698,244822830⟩]
theorem checked50564 : checkPrefixCuts (2^48) 6631456769 10 Manual.Count131072.C050564.packed 64 cuts50564 = true := by
 decide +kernel
def pointBounds50564 : List (Nat × Nat × Nat) := [(6631522304,111796567881817,111796955083333)]
theorem point_links_checked50564 : (cuts50564.take 1).map (fun c => (6631456769-1+2*2^10*c.k,111796445384972+c.lower,111796832586422+c.upper)) = pointBounds50564 := by
 decide +kernel
def cuts50565 : List PrefixCut := [⟨64,246303413,246303556⟩]
theorem checked50565 : checkPrefixCuts (2^48) 6631587841 10 Manual.Count131072.C050565.packed 64 cuts50565 = true := by
 decide +kernel
def cuts50566 : List PrefixCut := [⟨6,22240493,22240507⟩,
⟨64,243030399,243030538⟩]
theorem checked50566 : checkPrefixCuts (2^48) 6631718913 10 Manual.Count131072.C050566.packed 64 cuts50566 = true := by
 decide +kernel
def pointBounds50566 : List (Nat × Nat × Nat) := [(6631731200,111796958751576,111797345953315)]
theorem point_links_checked50566 : (cuts50566.take 1).map (fun c => (6631718913-1+2*2^10*c.k,111796936511083+c.lower,111797323712808+c.upper)) = pointBounds50566 := by
 decide +kernel
def cuts50567 : List PrefixCut := [⟨44,170534382,170534477⟩,
⟨64,247057639,247057776⟩]
theorem checked50567 : checkPrefixCuts (2^48) 6631849985 10 Manual.Count131072.C050567.packed 64 cuts50567 = true := by
 decide +kernel
def pointBounds50567 : List (Nat × Nat × Nat) := [(6631940096,111797350075864,111797737277823)]
theorem point_links_checked50567 : (cuts50567.take 1).map (fun c => (6631849985-1+2*2^10*c.k,111797179541482+c.lower,111797566743346+c.upper)) = pointBounds50567 := by
 decide +kernel
def cuts50568 : List PrefixCut := [⟨64,250999820,250999963⟩]
theorem checked50568 : checkPrefixCuts (2^48) 6631981057 10 Manual.Count131072.C050568.packed 64 cuts50568 = true := by
 decide +kernel
def cuts50569 : List PrefixCut := [⟨18,69263867,69263909⟩,
⟨64,247090318,247090466⟩]
theorem checked50569 : checkPrefixCuts (2^48) 6632112129 10 Manual.Count131072.C050569.packed 64 cuts50569 = true := by
 decide +kernel
def pointBounds50569 : List (Nat × Nat × Nat) := [(6632148992,111797746862808,111798134064994)]
theorem point_links_checked50569 : (cuts50569.take 1).map (fun c => (6632112129-1+2*2^10*c.k,111797677598941+c.lower,111798064801085+c.upper)) = pointBounds50569 := by
 decide +kernel
def cuts50570 : List PrefixCut := [⟨56,215722565,215722684⟩,
⟨64,245557599,245557734⟩]
theorem checked50570 : checkPrefixCuts (2^48) 6632243201 10 Manual.Count131072.C050570.packed 64 cuts50570 = true := by
 decide +kernel
def pointBounds50570 : List (Nat × Nat × Nat) := [(6632357888,111798140411824,111798527614235)]
theorem point_links_checked50570 : (cuts50570.take 1).map (fun c => (6632243201-1+2*2^10*c.k,111797924689259+c.lower,111798311891551+c.upper)) = pointBounds50570 := by
 decide +kernel
def cuts50571 : List PrefixCut := [⟨64,246613710,246613853⟩]
theorem checked50571 : checkPrefixCuts (2^48) 6632374273 10 Manual.Count131072.C050571.packed 64 cuts50571 = true := by
 decide +kernel
def cuts50572 : List PrefixCut := [⟨30,114032263,114032325⟩,
⟨64,246523956,246524094⟩]
theorem checked50572 : checkPrefixCuts (2^48) 6632505345 10 Manual.Count131072.C050572.packed 64 cuts50572 = true := by
 decide +kernel
def pointBounds50572 : List (Nat × Nat × Nat) := [(6632566784,111798530892831,111798918095463)]
theorem point_links_checked50572 : (cuts50572.take 1).map (fun c => (6632505345-1+2*2^10*c.k,111798416860568+c.lower,111798804063138+c.upper)) = pointBounds50572 := by
 decide +kernel
def cuts50573 : List PrefixCut := [⟨64,247410276,247410413⟩]
theorem checked50573 : checkPrefixCuts (2^48) 6632636417 10 Manual.Count131072.C050573.packed 64 cuts50573 = true := by
 decide +kernel
def cuts50574 : List PrefixCut := [⟨4,15828999,15829007⟩,
⟨64,242694919,242695059⟩]
theorem checked50574 : checkPrefixCuts (2^48) 6632767489 10 Manual.Count131072.C050574.packed 64 cuts50574 = true := by
 decide +kernel
def pointBounds50574 : List (Nat × Nat × Nat) := [(6632775680,111798926623799,111799313826652)]
theorem point_links_checked50574 : (cuts50574.take 1).map (fun c => (6632767489-1+2*2^10*c.k,111798910794800+c.lower,111799297997645+c.upper)) = pointBounds50574 := by
 decide +kernel
def cuts50575 : List PrefixCut := [⟨42,163208504,163208597⟩,
⟨64,247867308,247867447⟩]
theorem checked50575 : checkPrefixCuts (2^48) 6632898561 10 Manual.Count131072.C050575.packed 64 cuts50575 = true := by
 decide +kernel
def pointBounds50575 : List (Nat × Nat × Nat) := [(6632984576,111799316698223,111799703901301)]
theorem point_links_checked50575 : (cuts50575.take 1).map (fun c => (6632898561-1+2*2^10*c.k,111799153489719+c.lower,111799540692704+c.upper)) = pointBounds50575 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000017
