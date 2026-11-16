import PlattAssemblyKernel
import PlattCertificates.Count131072.C030640
import PlattCertificates.Count131072.C030641
import PlattCertificates.Count131072.C030642
import PlattCertificates.Count131072.C030643
import PlattCertificates.Count131072.C030644
import PlattCertificates.Count131072.C030645
import PlattCertificates.Count131072.C030646
import PlattCertificates.Count131072.C030647
import PlattCertificates.Count131072.C030648
import PlattCertificates.Count131072.C030649
import PlattCertificates.Count131072.C030650
import PlattCertificates.Count131072.C030651
import PlattCertificates.Count131072.C030652
import PlattCertificates.Count131072.C030653
import PlattCertificates.Count131072.C030654
import PlattCertificates.Count131072.C030655
import PlattCertificates.Count131072.C030656
import PlattCertificates.Count131072.C030657
import PlattCertificates.Count131072.C030658
import PlattCertificates.Count131072.C030659
import PlattCertificates.Count131072.C030660
import PlattCertificates.Count131072.C030661
import PlattCertificates.Count131072.C030662
import PlattCertificates.Count131072.C030663
import PlattCertificates.Count131072.C030664
import PlattCertificates.Count131072.C030665
import PlattCertificates.Count131072.C030666
import PlattCertificates.Count131072.C030667
import PlattCertificates.Count131072.C030668
import PlattCertificates.Count131072.C030669
import PlattCertificates.Count131072.C030670
import PlattCertificates.Count131072.C030671
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30640 : List PrefixCut := [⟨11,33959171,33959190⟩,
⟨128,415065872,415066107⟩]
theorem checked30640 : checkPrefixCuts (2^48) 4019978241 9 Manual.Count131072.C030640.packed 128 cuts30640 = true := by
 decide +kernel
def pointBounds30640 : List (Nat × Nat × Nat) := [(4019989504,105496510633730,105496894105943)]
theorem point_links_checked30640 : (cuts30640.take 1).map (fun c => (4019978241-1+2*2^9*c.k,105496476674559+c.lower,105496860146753+c.upper)) = pointBounds30640 := by
 decide +kernel
def cuts30641 : List PrefixCut := [⟨6,18624434,18624445⟩,
⟨128,413091960,413092195⟩]
theorem checked30641 : checkPrefixCuts (2^48) 4020109313 9 Manual.Count131072.C030641.packed 128 cuts30641 = true := by
 decide +kernel
def pointBounds30641 : List (Nat × Nat × Nat) := [(4020115456,105496910364865,105497293837305)]
theorem point_links_checked30641 : (cuts30641.take 1).map (fun c => (4020109313-1+2*2^9*c.k,105496891740431+c.lower,105497275212860+c.upper)) = pointBounds30641 := by
 decide +kernel
def cuts30642 : List PrefixCut := [⟨1,2940606,2940608⟩,
⟨124,404047006,404047233⟩,
⟨128,416089103,416089338⟩]
theorem checked30642 : checkPrefixCuts (2^48) 4020240385 9 Manual.Count131072.C030642.packed 128 cuts30642 = true := by
 decide +kernel
def pointBounds30642 : List (Nat × Nat × Nat) := [(4020241408,105497307772997,105497691245663),(4020367360,105497708879397,105498092352288)]
theorem point_links_checked30642 : (cuts30642.take 2).map (fun c => (4020240385-1+2*2^9*c.k,105497304832391+c.lower,105497688305055+c.upper)) = pointBounds30642 := by
 decide +kernel
def cuts30643 : List PrefixCut := [⟨119,390591953,390592164⟩,
⟨128,420556215,420556444⟩]
theorem checked30643 : checkPrefixCuts (2^48) 4020371457 9 Manual.Count131072.C030643.packed 128 cuts30643 = true := by
 decide +kernel
def pointBounds30643 : List (Nat × Nat × Nat) := [(4020493312,105498111513447,105498494986557)]
theorem point_links_checked30643 : (cuts30643.take 1).map (fun c => (4020371457-1+2*2^9*c.k,105497720921494+c.lower,105498104394393+c.upper)) = pointBounds30643 := by
 decide +kernel
def cuts30644 : List PrefixCut := [⟨114,368806702,368806911⟩,
⟨128,414451739,414451973⟩]
theorem checked30644 : checkPrefixCuts (2^48) 4020502529 9 Manual.Count131072.C030644.packed 128 cuts30644 = true := by
 decide +kernel
def pointBounds30644 : List (Nat × Nat × Nat) := [(4020619264,105498510284411,105498893757748)]
theorem point_links_checked30644 : (cuts30644.take 1).map (fun c => (4020502529-1+2*2^9*c.k,105498141477709+c.lower,105498524950837+c.upper)) = pointBounds30644 := by
 decide +kernel
def cuts30645 : List PrefixCut := [⟨109,356613760,356613957⟩,
⟨128,419128657,419128890⟩]
theorem checked30645 : checkPrefixCuts (2^48) 4020633601 9 Manual.Count131072.C030645.packed 128 cuts30645 = true := by
 decide +kernel
def pointBounds30645 : List (Nat × Nat × Nat) := [(4020745216,105498912543208,105499296016767)]
theorem point_links_checked30645 : (cuts30645.take 1).map (fun c => (4020633601-1+2*2^9*c.k,105498555929448+c.lower,105498939402810+c.upper)) = pointBounds30645 := by
 decide +kernel
def cuts30646 : List PrefixCut := [⟨104,339451284,339451472⟩,
⟨128,415124797,415125030⟩]
theorem checked30646 : checkPrefixCuts (2^48) 4020764673 9 Manual.Count131072.C030646.packed 128 cuts30646 = true := by
 decide +kernel
def pointBounds30646 : List (Nat × Nat × Nat) := [(4020871168,105499314509389,105499697983172)]
theorem point_links_checked30646 : (cuts30646.take 1).map (fun c => (4020764673-1+2*2^9*c.k,105498975058105+c.lower,105499358531700+c.upper)) = pointBounds30646 := by
 decide +kernel
def cuts30647 : List PrefixCut := [⟨99,320259802,320259981⟩,
⟨128,415321183,415321414⟩]
theorem checked30647 : checkPrefixCuts (2^48) 4020895745 9 Manual.Count131072.C030647.packed 128 cuts30647 = true := by
 decide +kernel
def pointBounds30647 : List (Nat × Nat × Nat) := [(4020997120,105499710442704,105500093916711)]
theorem point_links_checked30647 : (cuts30647.take 1).map (fun c => (4020895745-1+2*2^9*c.k,105499390182902+c.lower,105499773656730+c.upper)) = pointBounds30647 := by
 decide +kernel
def cuts30648 : List PrefixCut := [⟨94,304429612,304429786⟩,
⟨128,413837688,413837925⟩]
theorem checked30648 : checkPrefixCuts (2^48) 4021026817 9 Manual.Count131072.C030648.packed 128 cuts30648 = true := by
 decide +kernel
def pointBounds30648 : List (Nat × Nat × Nat) := [(4021123072,105500109933697,105500493407930)]
theorem point_links_checked30648 : (cuts30648.take 1).map (fun c => (4021026817-1+2*2^9*c.k,105499805504085+c.lower,105500188978144+c.upper)) = pointBounds30648 := by
 decide +kernel
def cuts30649 : List PrefixCut := [⟨89,289510411,289510576⟩,
⟨128,418234043,418234283⟩]
theorem checked30649 : checkPrefixCuts (2^48) 4021157889 9 Manual.Count131072.C030649.packed 128 cuts30649 = true := by
 decide +kernel
def pointBounds30649 : List (Nat × Nat × Nat) := [(4021249024,105500508852184,105500892326645)]
theorem point_links_checked30649 : (cuts30649.take 1).map (fun c => (4021157889-1+2*2^9*c.k,105500219341773+c.lower,105500602816069+c.upper)) = pointBounds30649 := by
 decide +kernel
def cuts30650 : List PrefixCut := [⟨84,273192210,273192369⟩,
⟨128,415000668,415000909⟩]
theorem checked30650 : checkPrefixCuts (2^48) 4021288961 9 Manual.Count131072.C030650.packed 128 cuts30650 = true := by
 decide +kernel
def pointBounds30650 : List (Nat × Nat × Nat) := [(4021374976,105500910768026,105501294242721)]
theorem point_links_checked30650 : (cuts30650.take 1).map (fun c => (4021288961-1+2*2^9*c.k,105500637575816+c.lower,105501021050352+c.upper)) = pointBounds30650 := by
 decide +kernel
def cuts30651 : List PrefixCut := [⟨79,256245128,256245272⟩,
⟨128,414077225,414077458⟩]
theorem checked30651 : checkPrefixCuts (2^48) 4021420033 9 Manual.Count131072.C030651.packed 128 cuts30651 = true := by
 decide +kernel
def pointBounds30651 : List (Nat × Nat × Nat) := [(4021500928,105501308821612,105501692296533)]
theorem point_links_checked30651 : (cuts30651.take 1).map (fun c => (4021420033-1+2*2^9*c.k,105501052576484+c.lower,105501436051261+c.upper)) = pointBounds30651 := by
 decide +kernel
def cuts30652 : List PrefixCut := [⟨74,241818804,241818941⟩,
⟨128,418403129,418403364⟩]
theorem checked30652 : checkPrefixCuts (2^48) 4021551105 9 Manual.Count131072.C030652.packed 128 cuts30652 = true := by
 decide +kernel
def pointBounds30652 : List (Nat × Nat × Nat) := [(4021626880,105501708472513,105502091947660)]
theorem point_links_checked30652 : (cuts30652.take 1).map (fun c => (4021551105-1+2*2^9*c.k,105501466653709+c.lower,105501850128719+c.upper)) = pointBounds30652 := by
 decide +kernel
def cuts30653 : List PrefixCut := [⟨69,220254552,220254677⟩,
⟨128,411110727,411110959⟩]
theorem checked30653 : checkPrefixCuts (2^48) 4021682177 9 Manual.Count131072.C030653.packed 128 cuts30653 = true := by
 decide +kernel
def pointBounds30653 : List (Nat × Nat × Nat) := [(4021752832,105502105311390,105502488786760)]
theorem point_links_checked30653 : (cuts30653.take 1).map (fun c => (4021682177-1+2*2^9*c.k,105501885056838+c.lower,105502268532083+c.upper)) = pointBounds30653 := by
 decide +kernel
def cuts30654 : List PrefixCut := [⟨64,211359206,211359323⟩,
⟨128,421035314,421035549⟩]
theorem checked30654 : checkPrefixCuts (2^48) 4021813249 9 Manual.Count131072.C030654.packed 128 cuts30654 = true := by
 decide +kernel
def pointBounds30654 : List (Nat × Nat × Nat) := [(4021878784,105502507526771,105502891002365)]
theorem point_links_checked30654 : (cuts30654.take 1).map (fun c => (4021813249-1+2*2^9*c.k,105502296167565+c.lower,105502679643042+c.upper)) = pointBounds30654 := by
 decide +kernel
def cuts30655 : List PrefixCut := [⟨59,187907718,187907822⟩,
⟨128,409264333,409264558⟩]
theorem checked30655 : checkPrefixCuts (2^48) 4021944321 9 Manual.Count131072.C030655.packed 128 cuts30655 = true := by
 decide +kernel
def pointBounds30655 : List (Nat × Nat × Nat) := [(4022004736,105502905110597,105503288586413)]
theorem point_links_checked30655 : (cuts30655.take 1).map (fun c => (4021944321-1+2*2^9*c.k,105502717202879+c.lower,105503100678591+c.upper)) = pointBounds30655 := by
 decide +kernel
def cuts30656 : List PrefixCut := [⟨54,177544389,177544488⟩,
⟨128,419258328,419258558⟩]
theorem checked30656 : checkPrefixCuts (2^48) 4022075393 9 Manual.Count131072.C030656.packed 128 cuts30656 = true := by
 decide +kernel
def pointBounds30656 : List (Nat × Nat × Nat) := [(4022130688,105503304011601,105503687487637)]
theorem point_links_checked30656 : (cuts30656.take 1).map (fun c => (4022075393-1+2*2^9*c.k,105503126467212+c.lower,105503509943149+c.upper)) = pointBounds30656 := by
 decide +kernel
def cuts30657 : List PrefixCut := [⟨49,159273992,159274082⟩,
⟨128,418684821,418685056⟩]
theorem checked30657 : checkPrefixCuts (2^48) 4022206465 9 Manual.Count131072.C030657.packed 128 cuts30657 = true := by
 decide +kernel
def pointBounds30657 : List (Nat × Nat × Nat) := [(4022256640,105503704999532,105504088475789)]
theorem point_links_checked30657 : (cuts30657.take 1).map (fun c => (4022206465-1+2*2^9*c.k,105503545725540+c.lower,105503929201707+c.upper)) = pointBounds30657 := by
 decide +kernel
def cuts30658 : List PrefixCut := [⟨44,141634555,141634634⟩,
⟨128,411813449,411813684⟩]
theorem checked30658 : checkPrefixCuts (2^48) 4022337537 9 Manual.Count131072.C030658.packed 128 cuts30658 = true := by
 decide +kernel
def pointBounds30658 : List (Nat × Nat × Nat) := [(4022382592,105504106044916,105504489521397)]
theorem point_links_checked30658 : (cuts30658.take 1).map (fun c => (4022337537-1+2*2^9*c.k,105503964410361+c.lower,105504347886763+c.upper)) = pointBounds30658 := by
 decide +kernel
def cuts30659 : List PrefixCut := [⟨39,127564995,127565071⟩,
⟨128,419077423,419077659⟩]
theorem checked30659 : checkPrefixCuts (2^48) 4022468609 9 Manual.Count131072.C030659.packed 128 cuts30659 = true := by
 decide +kernel
def pointBounds30659 : List (Nat × Nat × Nat) := [(4022508544,105504503788805,105504887265518)]
theorem point_links_checked30659 : (cuts30659.take 1).map (fun c => (4022468609-1+2*2^9*c.k,105504376223810+c.lower,105504759700447+c.upper)) = pointBounds30659 := by
 decide +kernel
def cuts30660 : List PrefixCut := [⟨34,109507869,109507930⟩,
⟨128,413535910,413536150⟩]
theorem checked30660 : checkPrefixCuts (2^48) 4022599681 9 Manual.Count131072.C030660.packed 128 cuts30660 = true := by
 decide +kernel
def pointBounds30660 : List (Nat × Nat × Nat) := [(4022634496,105504904809102,105505288286036)]
theorem point_links_checked30660 : (cuts30660.take 1).map (fun c => (4022599681-1+2*2^9*c.k,105504795301233+c.lower,105505178778106+c.upper)) = pointBounds30660 := by
 decide +kernel
def cuts30661 : List PrefixCut := [⟨29,93201152,93201208⟩,
⟨128,413802349,413802582⟩]
theorem checked30661 : checkPrefixCuts (2^48) 4022730753 9 Manual.Count131072.C030661.packed 128 cuts30661 = true := by
 decide +kernel
def pointBounds30661 : List (Nat × Nat × Nat) := [(4022760448,105505302038295,105505685515464)]
theorem point_links_checked30661 : (cuts30661.take 1).map (fun c => (4022730753-1+2*2^9*c.k,105505208837143+c.lower,105505592314256+c.upper)) = pointBounds30661 := by
 decide +kernel
def cuts30662 : List PrefixCut := [⟨24,76405717,76405760⟩,
⟨128,415258167,415258405⟩]
theorem checked30662 : checkPrefixCuts (2^48) 4022861825 9 Manual.Count131072.C030662.packed 128 cuts30662 = true := by
 decide +kernel
def pointBounds30662 : List (Nat × Nat × Nat) := [(4022886400,105505699045209,105506082522598)]
theorem point_links_checked30662 : (cuts30662.take 1).map (fun c => (4022861825-1+2*2^9*c.k,105505622639492+c.lower,105506006116838+c.upper)) = pointBounds30662 := by
 decide +kernel
def cuts30663 : List PrefixCut := [⟨19,62899767,62899803⟩,
⟨128,416084230,416084468⟩]
theorem checked30663 : checkPrefixCuts (2^48) 4022992897 9 Manual.Count131072.C030663.packed 128 cuts30663 = true := by
 decide +kernel
def pointBounds30663 : List (Nat × Nat × Nat) := [(4023012352,105506100797426,105506484275046)]
theorem point_links_checked30663 : (cuts30663.take 1).map (fun c => (4022992897-1+2*2^9*c.k,105506037897659+c.lower,105506421375243+c.upper)) = pointBounds30663 := by
 decide +kernel
def cuts30664 : List PrefixCut := [⟨14,42538193,42538218⟩,
⟨128,416980183,416980420⟩]
theorem checked30664 : checkPrefixCuts (2^48) 4023123969 9 Manual.Count131072.C030664.packed 128 cuts30664 = true := by
 decide +kernel
def pointBounds30664 : List (Nat × Nat × Nat) := [(4023138304,105506496520082,105506879997929)]
theorem point_links_checked30664 : (cuts30664.take 1).map (fun c => (4023123969-1+2*2^9*c.k,105506453981889+c.lower,105506837459711+c.upper)) = pointBounds30664 := by
 decide +kernel
def cuts30665 : List PrefixCut := [⟨9,27844837,27844854⟩,
⟨128,417106466,417106702⟩]
theorem checked30665 : checkPrefixCuts (2^48) 4023255041 9 Manual.Count131072.C030665.packed 128 cuts30665 = true := by
 decide +kernel
def pointBounds30665 : List (Nat × Nat × Nat) := [(4023264256,105506898806909,105507282284985)]
theorem point_links_checked30665 : (cuts30665.take 1).map (fun c => (4023255041-1+2*2^9*c.k,105506870962072+c.lower,105507254440131+c.upper)) = pointBounds30665 := by
 decide +kernel
def cuts30666 : List PrefixCut := [⟨4,10983668,10983674⟩,
⟨127,412125913,412126148⟩,
⟨128,414924210,414924447⟩]
theorem checked30666 : checkPrefixCuts (2^48) 4023386113 9 Manual.Count131072.C030666.packed 128 cuts30666 = true := by
 decide +kernel
def pointBounds30666 : List (Nat × Nat × Nat) := [(4023390208,105507299052206,105507682530507),(4023516160,105507700194451,105508083672981)]
theorem point_links_checked30666 : (cuts30666.take 2).map (fun c => (4023386113-1+2*2^9*c.k,105507288068538+c.lower,105507671546833+c.upper)) = pointBounds30666 := by
 decide +kernel
def cuts30667 : List PrefixCut := [⟨122,394413853,394414073⟩,
⟨128,415960055,415960286⟩]
theorem checked30667 : checkPrefixCuts (2^48) 4023517185 9 Manual.Count131072.C030667.packed 128 cuts30667 = true := by
 decide +kernel
def pointBounds30667 : List (Nat × Nat × Nat) := [(4023642112,105508097406601,105508480885353)]
theorem point_links_checked30667 : (cuts30667.take 1).map (fun c => (4023517185-1+2*2^9*c.k,105507702992748+c.lower,105508086471280+c.upper)) = pointBounds30667 := by
 decide +kernel
def cuts30668 : List PrefixCut := [⟨117,376982646,376982857⟩,
⟨128,411609364,411609595⟩]
theorem checked30668 : checkPrefixCuts (2^48) 4023648257 9 Manual.Count131072.C030668.packed 128 cuts30668 = true := by
 decide +kernel
def pointBounds30668 : List (Nat × Nat × Nat) := [(4023768064,105508495935449,105508879414423)]
theorem point_links_checked30668 : (cuts30668.take 1).map (fun c => (4023648257-1+2*2^9*c.k,105508118952803+c.lower,105508502431566+c.upper)) = pointBounds30668 := by
 decide +kernel
def cuts30669 : List PrefixCut := [⟨112,356194941,356195135⟩,
⟨128,407468829,407469050⟩]
theorem checked30669 : checkPrefixCuts (2^48) 4023779329 9 Manual.Count131072.C030669.packed 128 cuts30669 = true := by
 decide +kernel
def pointBounds30669 : List (Nat × Nat × Nat) := [(4023894016,105508886757108,105509270236296)]
theorem point_links_checked30669 : (cuts30669.take 1).map (fun c => (4023779329-1+2*2^9*c.k,105508530562167+c.lower,105508914041161+c.upper)) = pointBounds30669 := by
 decide +kernel
def cuts30670 : List PrefixCut := [⟨107,347509806,347509997⟩,
⟨128,414240675,414240906⟩]
theorem checked30670 : checkPrefixCuts (2^48) 4023910401 9 Manual.Count131072.C030670.packed 128 cuts30670 = true := by
 decide +kernel
def pointBounds30670 : List (Nat × Nat × Nat) := [(4024019968,105509285540802,105509669020208)]
theorem point_links_checked30670 : (cuts30670.take 1).map (fun c => (4023910401-1+2*2^9*c.k,105508938030996+c.lower,105509321510211+c.upper)) = pointBounds30670 := by
 decide +kernel
def cuts30671 : List PrefixCut := [⟨102,331550645,331550838⟩,
⟨128,417794383,417794622⟩]
theorem checked30671 : checkPrefixCuts (2^48) 4024041473 9 Manual.Count131072.C030671.packed 128 cuts30671 = true := by
 decide +kernel
def pointBounds30671 : List (Nat × Nat × Nat) := [(4024145920,105509683822316,105510067301955)]
theorem point_links_checked30671 : (cuts30671.take 1).map (fun c => (4024041473-1+2*2^9*c.k,105509352271671+c.lower,105509735751117+c.upper)) = pointBounds30671 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000020
