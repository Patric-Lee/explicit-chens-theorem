import PlattAssemblyKernel
import PlattCertificates.Count131072.C061696
import PlattCertificates.Count131072.C061697
import PlattCertificates.Count131072.C061698
import PlattCertificates.Count131072.C061699
import PlattCertificates.Count131072.C061700
import PlattCertificates.Count131072.C061701
import PlattCertificates.Count131072.C061702
import PlattCertificates.Count131072.C061703
import PlattCertificates.Count131072.C061704
import PlattCertificates.Count131072.C061705
import PlattCertificates.Count131072.C061706
import PlattCertificates.Count131072.C061707
import PlattCertificates.Count131072.C061708
import PlattCertificates.Count131072.C061709
import PlattCertificates.Count131072.C061710
import PlattCertificates.Count131072.C061711
import PlattCertificates.Count131072.C061712
import PlattCertificates.Count131072.C061713
import PlattCertificates.Count131072.C061714
import PlattCertificates.Count131072.C061715
import PlattCertificates.Count131072.C061716
import PlattCertificates.Count131072.C061717
import PlattCertificates.Count131072.C061718
import PlattCertificates.Count131072.C061719
import PlattCertificates.Count131072.C061720
import PlattCertificates.Count131072.C061721
import PlattCertificates.Count131072.C061722
import PlattCertificates.Count131072.C061723
import PlattCertificates.Count131072.C061724
import PlattCertificates.Count131072.C061725
import PlattCertificates.Count131072.C061726
import PlattCertificates.Count131072.C061727
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000053
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61696 : List PrefixCut := [⟨64,198095915,198096031⟩]
theorem checked61696 : checkPrefixCuts (2^48) 8090550273 10 Manual.Count131072.C061696.packed 64 cuts61696 = true := by
 decide +kernel
def cuts61697 : List PrefixCut := [⟨28,86070183,86070234⟩,
⟨64,201049829,201049946⟩]
theorem checked61697 : checkPrefixCuts (2^48) 8090681345 10 Manual.Count131072.C061697.packed 64 cuts61697 = true := by
 decide +kernel
def pointBounds61697 : List (Nat × Nat × Nat) := [(8090738688,114261077046716,114261465650935)]
theorem point_links_checked61697 : (cuts61697.take 1).map (fun c => (8090681345-1+2*2^10*c.k,114260990976533+c.lower,114261379580701+c.upper)) = pointBounds61697 := by
 decide +kernel
def cuts61698 : List PrefixCut := [⟨64,199620226,199620342⟩]
theorem checked61698 : checkPrefixCuts (2^48) 8090812417 10 Manual.Count131072.C061698.packed 64 cuts61698 = true := by
 decide +kernel
def cuts61699 : List PrefixCut := [⟨24,74065306,74065348⟩,
⟨64,198155876,198155992⟩]
theorem checked61699 : checkPrefixCuts (2^48) 8090943489 10 Manual.Count131072.C061699.packed 64 cuts61699 = true := by
 decide +kernel
def pointBounds61699 : List (Nat × Nat × Nat) := [(8090992640,114261465711894,114261854316337)]
theorem point_links_checked61699 : (cuts61699.take 1).map (fun c => (8090943489-1+2*2^10*c.k,114261391646588+c.lower,114261780250989+c.upper)) = pointBounds61699 := by
 decide +kernel
def cuts61700 : List PrefixCut := [⟨64,197665642,197665756⟩]
theorem checked61700 : checkPrefixCuts (2^48) 8091074561 10 Manual.Count131072.C061700.packed 64 cuts61700 = true := by
 decide +kernel
def cuts61701 : List PrefixCut := [⟨20,63452706,63452745⟩,
⟨64,202219595,202219713⟩]
theorem checked61701 : checkPrefixCuts (2^48) 8091205633 10 Manual.Count131072.C061701.packed 64 cuts61701 = true := by
 decide +kernel
def pointBounds61701 : List (Nat × Nat × Nat) := [(8091246592,114261850920812,114262239525482)]
theorem point_links_checked61701 : (cuts61701.take 1).map (fun c => (8091205633-1+2*2^10*c.k,114261787468106+c.lower,114262176072737+c.upper)) = pointBounds61701 := by
 decide +kernel
def cuts61702 : List PrefixCut := [⟨64,199989965,199990087⟩]
theorem checked61702 : checkPrefixCuts (2^48) 8091336705 10 Manual.Count131072.C061702.packed 64 cuts61702 = true := by
 decide +kernel
def cuts61703 : List PrefixCut := [⟨16,49049051,49049078⟩,
⟨64,200265001,200265116⟩]
theorem checked61703 : checkPrefixCuts (2^48) 8091467777 10 Manual.Count131072.C061703.packed 64 cuts61703 = true := by
 decide +kernel
def pointBounds61703 : List (Nat × Nat × Nat) := [(8091500544,114262238726717,114262627331615)]
theorem point_links_checked61703 : (cuts61703.take 1).map (fun c => (8091467777-1+2*2^10*c.k,114262189677666+c.lower,114262578282537+c.upper)) = pointBounds61703 := by
 decide +kernel
def cuts61704 : List PrefixCut := [⟨64,200296562,200296679⟩]
theorem checked61704 : checkPrefixCuts (2^48) 8091598849 10 Manual.Count131072.C061704.packed 64 cuts61704 = true := by
 decide +kernel
def cuts61705 : List PrefixCut := [⟨12,37811784,37811808⟩,
⟨64,198206205,198206317⟩]
theorem checked61705 : checkPrefixCuts (2^48) 8091729921 10 Manual.Count131072.C061705.packed 64 cuts61705 = true := by
 decide +kernel
def pointBounds61705 : List (Nat × Nat × Nat) := [(8091754496,114262628051013,114263016656140)]
theorem point_links_checked61705 : (cuts61705.take 1).map (fun c => (8091729921-1+2*2^10*c.k,114262590239229+c.lower,114262978844332+c.upper)) = pointBounds61705 := by
 decide +kernel
def cuts61706 : List PrefixCut := [⟨64,200533541,200533660⟩]
theorem checked61706 : checkPrefixCuts (2^48) 8091860993 10 Manual.Count131072.C061706.packed 64 cuts61706 = true := by
 decide +kernel
def cuts61707 : List PrefixCut := [⟨8,25288216,25288231⟩,
⟨64,199904198,199904311⟩]
theorem checked61707 : checkPrefixCuts (2^48) 8091992065 10 Manual.Count131072.C061707.packed 64 cuts61707 = true := by
 decide +kernel
def pointBounds61707 : List (Nat × Nat × Nat) := [(8092008448,114263014267191,114263402872540)]
theorem point_links_checked61707 : (cuts61707.take 1).map (fun c => (8091992065-1+2*2^10*c.k,114262988978975+c.lower,114263377584309+c.upper)) = pointBounds61707 := by
 decide +kernel
def cuts61708 : List PrefixCut := [⟨64,199344420,199344531⟩]
theorem checked61708 : checkPrefixCuts (2^48) 8092123137 10 Manual.Count131072.C061708.packed 64 cuts61708 = true := by
 decide +kernel
def cuts61709 : List PrefixCut := [⟨4,12139347,12139355⟩,
⟨64,198297669,198297787⟩]
theorem checked61709 : checkPrefixCuts (2^48) 8092254209 10 Manual.Count131072.C061709.packed 64 cuts61709 = true := by
 decide +kernel
def pointBounds61709 : List (Nat × Nat × Nat) := [(8092262400,114263400366940,114263788972506)]
theorem point_links_checked61709 : (cuts61709.take 1).map (fun c => (8092254209-1+2*2^10*c.k,114263388227593+c.lower,114263776833151+c.upper)) = pointBounds61709 := by
 decide +kernel
def cuts61710 : List PrefixCut := [⟨64,200311863,200311974⟩]
theorem checked61710 : checkPrefixCuts (2^48) 8092385281 10 Manual.Count131072.C061710.packed 64 cuts61710 = true := by
 decide +kernel
def pointBounds61710 : List (Nat × Nat × Nat) := [(8092516352,114263786837125,114264175442912)]
theorem point_links_checked61710 : (cuts61710.take 1).map (fun c => (8092385281-1+2*2^10*c.k,114263586525262+c.lower,114263975130938+c.upper)) = pointBounds61710 := by
 decide +kernel
def cuts61711 : List PrefixCut := [⟨64,200830347,200830460⟩]
theorem checked61711 : checkPrefixCuts (2^48) 8092516353 10 Manual.Count131072.C061711.packed 64 cuts61711 = true := by
 decide +kernel
def cuts61712 : List PrefixCut := [⟨60,188062461,188062571⟩,
⟨64,200270598,200270713⟩]
theorem checked61712 : checkPrefixCuts (2^48) 8092647425 10 Manual.Count131072.C061712.packed 64 cuts61712 = true := by
 decide +kernel
def pointBounds61712 : List (Nat × Nat × Nat) := [(8092770304,114264175729933,114264564335943)]
theorem point_links_checked61712 : (cuts61712.take 1).map (fun c => (8092647425-1+2*2^10*c.k,114263987667472+c.lower,114264376273372+c.upper)) = pointBounds61712 := by
 decide +kernel
def cuts61713 : List PrefixCut := [⟨64,200649943,200650056⟩]
theorem checked61713 : checkPrefixCuts (2^48) 8092778497 10 Manual.Count131072.C061713.packed 64 cuts61713 = true := by
 decide +kernel
def cuts61714 : List PrefixCut := [⟨56,176579010,176579109⟩,
⟨64,201446641,201446755⟩]
theorem checked61714 : checkPrefixCuts (2^48) 8092909569 10 Manual.Count131072.C061714.packed 64 cuts61714 = true := by
 decide +kernel
def pointBounds61714 : List (Nat × Nat × Nat) := [(8093024256,114264565167023,114264953773250)]
theorem point_links_checked61714 : (cuts61714.take 1).map (fun c => (8092909569-1+2*2^10*c.k,114264388588013+c.lower,114264777194141+c.upper)) = pointBounds61714 := by
 decide +kernel
def cuts61715 : List PrefixCut := [⟨64,202069410,202069524⟩]
theorem checked61715 : checkPrefixCuts (2^48) 8093040641 10 Manual.Count131072.C061715.packed 64 cuts61715 = true := by
 decide +kernel
def cuts61716 : List PrefixCut := [⟨52,162174842,162174940⟩,
⟨64,199492488,199492610⟩]
theorem checked61716 : checkPrefixCuts (2^48) 8093171713 10 Manual.Count131072.C061716.packed 64 cuts61716 = true := by
 decide +kernel
def pointBounds61716 : List (Nat × Nat × Nat) := [(8093278208,114264954278906,114265342885360)]
theorem point_links_checked61716 : (cuts61716.take 1).map (fun c => (8093171713-1+2*2^10*c.k,114264792104064+c.lower,114265180710420+c.upper)) = pointBounds61716 := by
 decide +kernel
def cuts61717 : List PrefixCut := [⟨64,200323938,200324056⟩]
theorem checked61717 : checkPrefixCuts (2^48) 8093302785 10 Manual.Count131072.C061717.packed 64 cuts61717 = true := by
 decide +kernel
def cuts61718 : List PrefixCut := [⟨48,148188933,148189019⟩,
⟨64,198999135,198999249⟩]
theorem checked61718 : checkPrefixCuts (2^48) 8093433857 10 Manual.Count131072.C061718.packed 64 cuts61718 = true := by
 decide +kernel
def pointBounds61718 : List (Nat × Nat × Nat) := [(8093532160,114265340109423,114265728716105)]
theorem point_links_checked61718 : (cuts61718.take 1).map (fun c => (8093433857-1+2*2^10*c.k,114265191920490+c.lower,114265580527086+c.upper)) = pointBounds61718 := by
 decide +kernel
def cuts61719 : List PrefixCut := [⟨64,199135024,199135143⟩]
theorem checked61719 : checkPrefixCuts (2^48) 8093564929 10 Manual.Count131072.C061719.packed 64 cuts61719 = true := by
 decide +kernel
def cuts61720 : List PrefixCut := [⟨44,137299041,137299122⟩,
⟨64,202157357,202157475⟩]
theorem checked61720 : checkPrefixCuts (2^48) 8093696001 10 Manual.Count131072.C061720.packed 64 cuts61720 = true := by
 decide +kernel
def pointBounds61720 : List (Nat × Nat × Nat) := [(8093786112,114265727353690,114266115960600)]
theorem point_links_checked61720 : (cuts61720.take 1).map (fun c => (8093696001-1+2*2^10*c.k,114265590054649+c.lower,114265978661478+c.upper)) = pointBounds61720 := by
 decide +kernel
def cuts61721 : List PrefixCut := [⟨64,197424536,197424645⟩]
theorem checked61721 : checkPrefixCuts (2^48) 8093827073 10 Manual.Count131072.C061721.packed 64 cuts61721 = true := by
 decide +kernel
def cuts61722 : List PrefixCut := [⟨40,123593018,123593088⟩,
⟨64,198673258,198673371⟩]
theorem checked61722 : checkPrefixCuts (2^48) 8093958145 10 Manual.Count131072.C061722.packed 64 cuts61722 = true := by
 decide +kernel
def pointBounds61722 : List (Nat × Nat × Nat) := [(8094040064,114266113229560,114266501836686)]
theorem point_links_checked61722 : (cuts61722.take 1).map (fun c => (8093958145-1+2*2^10*c.k,114265989636542+c.lower,114266378243598+c.upper)) = pointBounds61722 := by
 decide +kernel
def cuts61723 : List PrefixCut := [⟨64,203121250,203121364⟩]
theorem checked61723 : checkPrefixCuts (2^48) 8094089217 10 Manual.Count131072.C061723.packed 64 cuts61723 = true := by
 decide +kernel
def cuts61724 : List PrefixCut := [⟨36,112565513,112565580⟩,
⟨64,201135813,201135928⟩]
theorem checked61724 : checkPrefixCuts (2^48) 8094220289 10 Manual.Count131072.C061724.packed 64 cuts61724 = true := by
 decide +kernel
def pointBounds61724 : List (Nat × Nat × Nat) := [(8094294016,114266503996563,114266892603913)]
theorem point_links_checked61724 : (cuts61724.take 1).map (fun c => (8094220289-1+2*2^10*c.k,114266391431050+c.lower,114266780038333+c.upper)) = pointBounds61724 := by
 decide +kernel
def cuts61725 : List PrefixCut := [⟨64,198872261,198872376⟩]
theorem checked61725 : checkPrefixCuts (2^48) 8094351361 10 Manual.Count131072.C061725.packed 64 cuts61725 = true := by
 decide +kernel
def cuts61726 : List PrefixCut := [⟨32,100043455,100043515⟩,
⟨64,200851114,200851232⟩]
theorem checked61726 : checkPrefixCuts (2^48) 8094482433 10 Manual.Count131072.C061726.packed 64 cuts61726 = true := by
 decide +kernel
def pointBounds61726 : List (Nat × Nat × Nat) := [(8094547968,114266891482579,114267280090152)]
theorem point_links_checked61726 : (cuts61726.take 1).map (fun c => (8094482433-1+2*2^10*c.k,114266791439124+c.lower,114267180046637+c.upper)) = pointBounds61726 := by
 decide +kernel
def cuts61727 : List PrefixCut := [⟨64,197509674,197509788⟩]
theorem checked61727 : checkPrefixCuts (2^48) 8094613505 10 Manual.Count131072.C061727.packed 64 cuts61727 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000053
