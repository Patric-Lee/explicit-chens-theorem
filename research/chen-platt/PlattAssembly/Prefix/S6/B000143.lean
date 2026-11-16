import PlattAssemblyKernel
import PlattCertificates.Count131072.C054576
import PlattCertificates.Count131072.C054577
import PlattCertificates.Count131072.C054578
import PlattCertificates.Count131072.C054579
import PlattCertificates.Count131072.C054580
import PlattCertificates.Count131072.C054581
import PlattCertificates.Count131072.C054582
import PlattCertificates.Count131072.C054583
import PlattCertificates.Count131072.C054584
import PlattCertificates.Count131072.C054585
import PlattCertificates.Count131072.C054586
import PlattCertificates.Count131072.C054587
import PlattCertificates.Count131072.C054588
import PlattCertificates.Count131072.C054589
import PlattCertificates.Count131072.C054590
import PlattCertificates.Count131072.C054591
import PlattCertificates.Count131072.C054592
import PlattCertificates.Count131072.C054593
import PlattCertificates.Count131072.C054594
import PlattCertificates.Count131072.C054595
import PlattCertificates.Count131072.C054596
import PlattCertificates.Count131072.C054597
import PlattCertificates.Count131072.C054598
import PlattCertificates.Count131072.C054599
import PlattCertificates.Count131072.C054600
import PlattCertificates.Count131072.C054601
import PlattCertificates.Count131072.C054602
import PlattCertificates.Count131072.C054603
import PlattCertificates.Count131072.C054604
import PlattCertificates.Count131072.C054605
import PlattCertificates.Count131072.C054606
import PlattCertificates.Count131072.C054607
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000143
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54576 : List PrefixCut := [⟨64,228958945,228959074⟩]
theorem checked54576 : checkPrefixCuts (2^48) 7157317633 10 Manual.Count131072.C054576.packed 64 cuts54576 = true := by
 decide +kernel
def cuts54577 : List PrefixCut := [⟨35,125213818,125213888⟩,
⟨64,227106437,227106564⟩]
theorem checked54577 : checkPrefixCuts (2^48) 7157448705 10 Manual.Count131072.C054577.packed 64 cuts54577 = true := by
 decide +kernel
def pointBounds54577 : List (Nat × Nat × Nat) := [(7157520384,112744971021415,112745358761758)]
theorem point_links_checked54577 : (cuts54577.take 1).map (fun c => (7157448705-1+2*2^10*c.k,112744845807597+c.lower,112745233547870+c.upper)) = pointBounds54577 := by
 decide +kernel
def cuts54578 : List PrefixCut := [⟨64,225332648,225332774⟩]
theorem checked54578 : checkPrefixCuts (2^48) 7157579777 10 Manual.Count131072.C054578.packed 64 cuts54578 = true := by
 decide +kernel
def cuts54579 : List PrefixCut := [⟨17,60953152,60953187⟩,
⟨64,226508259,226508385⟩]
theorem checked54579 : checkPrefixCuts (2^48) 7157710849 10 Manual.Count131072.C054579.packed 64 cuts54579 = true := by
 decide +kernel
def pointBounds54579 : List (Nat × Nat × Nat) := [(7157745664,112745359199834,112745746940395)]
theorem point_links_checked54579 : (cuts54579.take 1).map (fun c => (7157710849-1+2*2^10*c.k,112745298246682+c.lower,112745685987208+c.upper)) = pointBounds54579 := by
 decide +kernel
def cuts54580 : List PrefixCut := [⟨63,222414470,222414600⟩,
⟨64,226189504,226189636⟩]
theorem checked54580 : checkPrefixCuts (2^48) 7157841921 10 Manual.Count131072.C054580.packed 64 cuts54580 = true := by
 decide +kernel
def pointBounds54580 : List (Nat × Nat × Nat) := [(7157970944,112745747169411,112746134910193)]
theorem point_links_checked54580 : (cuts54580.take 1).map (fun c => (7157841921-1+2*2^10*c.k,112745524754941+c.lower,112745912495593+c.upper)) = pointBounds54580 := by
 decide +kernel
def cuts54581 : List PrefixCut := [⟨64,223275468,223275596⟩]
theorem checked54581 : checkPrefixCuts (2^48) 7157972993 10 Manual.Count131072.C054581.packed 64 cuts54581 = true := by
 decide +kernel
def cuts54582 : List PrefixCut := [⟨45,156188164,156188254⟩,
⟨64,223703928,223704056⟩]
theorem checked54582 : checkPrefixCuts (2^48) 7158104065 10 Manual.Count131072.C054582.packed 64 cuts54582 = true := by
 decide +kernel
def pointBounds54582 : List (Nat × Nat × Nat) := [(7158196224,112746130408077,112746518149079)]
theorem point_links_checked54582 : (cuts54582.take 1).map (fun c => (7158104065-1+2*2^10*c.k,112745974219913+c.lower,112746361960825+c.upper)) = pointBounds54582 := by
 decide +kernel
def cuts54583 : List PrefixCut := [⟨64,226137772,226137900⟩]
theorem checked54583 : checkPrefixCuts (2^48) 7158235137 10 Manual.Count131072.C054583.packed 64 cuts54583 = true := by
 decide +kernel
def cuts54584 : List PrefixCut := [⟨27,98027141,98027195⟩,
⟨64,227391908,227392037⟩]
theorem checked54584 : checkPrefixCuts (2^48) 7158366209 10 Manual.Count131072.C054584.packed 64 cuts54584 = true := by
 decide +kernel
def pointBounds54584 : List (Nat × Nat × Nat) := [(7158421504,112746522088754,112746909829976)]
theorem point_links_checked54584 : (cuts54584.take 1).map (fun c => (7158366209-1+2*2^10*c.k,112746424061613+c.lower,112746811802781+c.upper)) = pointBounds54584 := by
 decide +kernel
def cuts54585 : List PrefixCut := [⟨64,225539684,225539811⟩]
theorem checked54585 : checkPrefixCuts (2^48) 7158497281 10 Manual.Count131072.C054585.packed 64 cuts54585 = true := by
 decide +kernel
def cuts54586 : List PrefixCut := [⟨9,32281407,32281426⟩,
⟨64,227304926,227305058⟩]
theorem checked54586 : checkPrefixCuts (2^48) 7158628353 10 Manual.Count131072.C054586.packed 64 cuts54586 = true := by
 decide +kernel
def pointBounds54586 : List (Nat × Nat × Nat) := [(7158646784,112746909274612,112747297016055)]
theorem point_links_checked54586 : (cuts54586.take 1).map (fun c => (7158628353-1+2*2^10*c.k,112746876993205+c.lower,112747264734629+c.upper)) = pointBounds54586 := by
 decide +kernel
def cuts54587 : List PrefixCut := [⟨55,197340258,197340369⟩,
⟨64,228676928,228677057⟩]
theorem checked54587 : checkPrefixCuts (2^48) 7158759425 10 Manual.Count131072.C054587.packed 64 cuts54587 = true := by
 decide +kernel
def pointBounds54587 : List (Nat × Nat × Nat) := [(7158872064,112747301638389,112747689380056)]
theorem point_links_checked54587 : (cuts54587.take 1).map (fun c => (7158759425-1+2*2^10*c.k,112747104298131+c.lower,112747492039687+c.upper)) = pointBounds54587 := by
 decide +kernel
def cuts54588 : List PrefixCut := [⟨64,227375229,227375361⟩]
theorem checked54588 : checkPrefixCuts (2^48) 7158890497 10 Manual.Count131072.C054588.packed 64 cuts54588 = true := by
 decide +kernel
def cuts54589 : List PrefixCut := [⟨37,130572745,130572819⟩,
⟨64,227095834,227095962⟩]
theorem checked54589 : checkPrefixCuts (2^48) 7159021569 10 Manual.Count131072.C054589.packed 64 cuts54589 = true := by
 decide +kernel
def pointBounds54589 : List (Nat × Nat × Nat) := [(7159097344,112747690923033,112748078664924)]
theorem point_links_checked54589 : (cuts54589.take 1).map (fun c => (7159021569-1+2*2^10*c.k,112747560350288+c.lower,112747948092105+c.upper)) = pointBounds54589 := by
 decide +kernel
def cuts54590 : List PrefixCut := [⟨64,226108794,226108922⟩]
theorem checked54590 : checkPrefixCuts (2^48) 7159152641 10 Manual.Count131072.C054590.packed 64 cuts54590 = true := by
 decide +kernel
def cuts54591 : List PrefixCut := [⟨19,67308927,67308967⟩,
⟨64,223981610,223981739⟩]
theorem checked54591 : checkPrefixCuts (2^48) 7159283713 10 Manual.Count131072.C054591.packed 64 cuts54591 = true := by
 decide +kernel
def pointBounds54591 : List (Nat × Nat × Nat) := [(7159322624,112748080863843,112748468605956)]
theorem point_links_checked54591 : (cuts54591.take 1).map (fun c => (7159283713-1+2*2^10*c.k,112748013554916+c.lower,112748401296989+c.upper)) = pointBounds54591 := by
 decide +kernel
def cuts54592 : List PrefixCut := [⟨64,228184209,228184338⟩]
theorem checked54592 : checkPrefixCuts (2^48) 7159414785 10 Manual.Count131072.C054592.packed 64 cuts54592 = true := by
 decide +kernel
def cuts54593 : List PrefixCut := [⟨1,3892148,3892150⟩,
⟨64,228337273,228337402⟩]
theorem checked54593 : checkPrefixCuts (2^48) 7159545857 10 Manual.Count131072.C054593.packed 64 cuts54593 = true := by
 decide +kernel
def pointBounds54593 : List (Nat × Nat × Nat) := [(7159547904,112748469612883,112748857355216)]
theorem point_links_checked54593 : (cuts54593.take 1).map (fun c => (7159545857-1+2*2^10*c.k,112748465720735+c.lower,112748853463066+c.upper)) = pointBounds54593 := by
 decide +kernel
def cuts54594 : List PrefixCut := [⟨47,166925740,166925834⟩,
⟨64,225974301,225974428⟩]
theorem checked54594 : checkPrefixCuts (2^48) 7159676929 10 Manual.Count131072.C054594.packed 64 cuts54594 = true := by
 decide +kernel
def pointBounds54594 : List (Nat × Nat × Nat) := [(7159773184,112748860983748,112749248726302)]
theorem point_links_checked54594 : (cuts54594.take 1).map (fun c => (7159676929-1+2*2^10*c.k,112748694058008+c.lower,112749081800468+c.upper)) = pointBounds54594 := by
 decide +kernel
def cuts54595 : List PrefixCut := [⟨64,226441884,226442009⟩]
theorem checked54595 : checkPrefixCuts (2^48) 7159808001 10 Manual.Count131072.C054595.packed 64 cuts54595 = true := by
 decide +kernel
def cuts54596 : List PrefixCut := [⟨29,103587928,103587989⟩,
⟨64,227066761,227066892⟩]
theorem checked54596 : checkPrefixCuts (2^48) 7159939073 10 Manual.Count131072.C054596.packed 64 cuts54596 = true := by
 decide +kernel
def pointBounds54596 : List (Nat × Nat × Nat) := [(7159998464,112749250062121,112749637804894)]
theorem point_links_checked54596 : (cuts54596.take 1).map (fun c => (7159939073-1+2*2^10*c.k,112749146474193+c.lower,112749534216905+c.upper)) = pointBounds54596 := by
 decide +kernel
def cuts54597 : List PrefixCut := [⟨64,229264011,229264140⟩]
theorem checked54597 : checkPrefixCuts (2^48) 7160070145 10 Manual.Count131072.C054597.packed 64 cuts54597 = true := by
 decide +kernel
def cuts54598 : List PrefixCut := [⟨11,38721304,38721327⟩,
⟨64,224739107,224739240⟩]
theorem checked54598 : checkPrefixCuts (2^48) 7160201217 10 Manual.Count131072.C054598.packed 64 cuts54598 = true := by
 decide +kernel
def pointBounds54598 : List (Nat × Nat × Nat) := [(7160223744,112749641526269,112750029269264)]
theorem point_links_checked54598 : (cuts54598.take 1).map (fun c => (7160201217-1+2*2^10*c.k,112749602804965+c.lower,112749990547937+c.upper)) = pointBounds54598 := by
 decide +kernel
def cuts54599 : List PrefixCut := [⟨57,200048551,200048664⟩,
⟨64,225442572,225442699⟩]
theorem checked54599 : checkPrefixCuts (2^48) 7160332289 10 Manual.Count131072.C054599.packed 64 cuts54599 = true := by
 decide +kernel
def pointBounds54599 : List (Nat × Nat × Nat) := [(7160449024,112750027592623,112750415335841)]
theorem point_links_checked54599 : (cuts54599.take 1).map (fun c => (7160332289-1+2*2^10*c.k,112749827544072+c.lower,112750215287177+c.upper)) = pointBounds54599 := by
 decide +kernel
def cuts54600 : List PrefixCut := [⟨64,227207362,227207492⟩]
theorem checked54600 : checkPrefixCuts (2^48) 7160463361 10 Manual.Count131072.C054600.packed 64 cuts54600 = true := by
 decide +kernel
def cuts54601 : List PrefixCut := [⟨39,139191954,139192033⟩,
⟨64,226534985,226535115⟩]
theorem checked54601 : checkPrefixCuts (2^48) 7160594433 10 Manual.Count131072.C054601.packed 64 cuts54601 = true := by
 decide +kernel
def pointBounds54601 : List (Nat × Nat × Nat) := [(7160674304,112750419385960,112750807129401)]
theorem point_links_checked54601 : (cuts54601.take 1).map (fun c => (7160594433-1+2*2^10*c.k,112750280194006+c.lower,112750667937368+c.upper)) = pointBounds54601 := by
 decide +kernel
def cuts54602 : List PrefixCut := [⟨64,227434911,227435041⟩]
theorem checked54602 : checkPrefixCuts (2^48) 7160725505 10 Manual.Count131072.C054602.packed 64 cuts54602 = true := by
 decide +kernel
def cuts54603 : List PrefixCut := [⟨21,74565983,74566025⟩,
⟨64,229828464,229828594⟩]
theorem checked54603 : checkPrefixCuts (2^48) 7160856577 10 Manual.Count131072.C054603.packed 64 cuts54603 = true := by
 decide +kernel
def pointBounds54603 : List (Nat × Nat × Nat) := [(7160899584,112750808729885,112751196473549)]
theorem point_links_checked54603 : (cuts54603.take 1).map (fun c => (7160856577-1+2*2^10*c.k,112750734163902+c.lower,112751121907524+c.upper)) = pointBounds54603 := by
 decide +kernel
def cuts54604 : List PrefixCut := [⟨64,226954909,226955041⟩]
theorem checked54604 : checkPrefixCuts (2^48) 7160987649 10 Manual.Count131072.C054604.packed 64 cuts54604 = true := by
 decide +kernel
def cuts54605 : List PrefixCut := [⟨3,11241510,11241516⟩,
⟨64,228169221,228169354⟩]
theorem checked54605 : checkPrefixCuts (2^48) 7161118721 10 Manual.Count131072.C054605.packed 64 cuts54605 = true := by
 decide +kernel
def pointBounds54605 : List (Nat × Nat × Nat) := [(7161124864,112751202188785,112751589932675)]
theorem point_links_checked54605 : (cuts54605.take 1).map (fun c => (7161118721-1+2*2^10*c.k,112751190947275+c.lower,112751578691159+c.upper)) = pointBounds54605 := by
 decide +kernel
def cuts54606 : List PrefixCut := [⟨49,172745469,172745565⟩,
⟨64,225767429,225767556⟩]
theorem checked54606 : checkPrefixCuts (2^48) 7161249793 10 Manual.Count131072.C054606.packed 64 cuts54606 = true := by
 decide +kernel
def pointBounds54606 : List (Nat × Nat × Nat) := [(7161350144,112751591861965,112751979606078)]
theorem point_links_checked54606 : (cuts54606.take 1).map (fun c => (7161249793-1+2*2^10*c.k,112751419116496+c.lower,112751806860513+c.upper)) = pointBounds54606 := by
 decide +kernel
def cuts54607 : List PrefixCut := [⟨64,229733023,229733153⟩]
theorem checked54607 : checkPrefixCuts (2^48) 7161380865 10 Manual.Count131072.C054607.packed 64 cuts54607 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000143
