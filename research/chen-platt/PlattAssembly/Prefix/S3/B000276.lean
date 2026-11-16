import PlattAssemblyKernel
import PlattCertificates.Count131072.C028832
import PlattCertificates.Count131072.C028833
import PlattCertificates.Count131072.C028834
import PlattCertificates.Count131072.C028835
import PlattCertificates.Count131072.C028836
import PlattCertificates.Count131072.C028837
import PlattCertificates.Count131072.C028838
import PlattCertificates.Count131072.C028839
import PlattCertificates.Count131072.C028840
import PlattCertificates.Count131072.C028841
import PlattCertificates.Count131072.C028842
import PlattCertificates.Count131072.C028843
import PlattCertificates.Count131072.C028844
import PlattCertificates.Count131072.C028845
import PlattCertificates.Count131072.C028846
import PlattCertificates.Count131072.C028847
import PlattCertificates.Count131072.C028848
import PlattCertificates.Count131072.C028849
import PlattCertificates.Count131072.C028850
import PlattCertificates.Count131072.C028851
import PlattCertificates.Count131072.C028852
import PlattCertificates.Count131072.C028853
import PlattCertificates.Count131072.C028854
import PlattCertificates.Count131072.C028855
import PlattCertificates.Count131072.C028856
import PlattCertificates.Count131072.C028857
import PlattCertificates.Count131072.C028858
import PlattCertificates.Count131072.C028859
import PlattCertificates.Count131072.C028860
import PlattCertificates.Count131072.C028861
import PlattCertificates.Count131072.C028862
import PlattCertificates.Count131072.C028863
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000276
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28832 : List PrefixCut := [⟨39,131622110,131622182⟩,
⟨128,439503910,439504149⟩]
theorem checked28832 : checkPrefixCuts (2^48) 3783000065 9 Manual.Count131072.C028832.packed 128 cuts28832 = true := by
 decide +kernel
def pointBounds28832 : List (Nat × Nat × Nat) := [(3783040000,104722316281689,104722699319389)]
theorem point_links_checked28832 : (cuts28832.take 1).map (fun c => (3783000065-1+2*2^9*c.k,104722184659579+c.lower,104722567697207+c.upper)) = pointBounds28832 := by
 decide +kernel
def cuts28833 : List PrefixCut := [⟨27,93077346,93077401⟩,
⟨128,441869518,441869771⟩]
theorem checked28833 : checkPrefixCuts (2^48) 3783131137 9 Manual.Count131072.C028833.packed 128 cuts28833 = true := by
 decide +kernel
def pointBounds28833 : List (Nat × Nat × Nat) := [(3783158784,104722717240835,104723100278757)]
theorem point_links_checked28833 : (cuts28833.take 1).map (fun c => (3783131137-1+2*2^9*c.k,104722624163489+c.lower,104723007201356+c.upper)) = pointBounds28833 := by
 decide +kernel
def cuts28834 : List PrefixCut := [⟨15,50740733,50740762⟩,
⟨128,438431860,438432108⟩]
theorem checked28834 : checkPrefixCuts (2^48) 3783262209 9 Manual.Count131072.C028834.packed 128 cuts28834 = true := by
 decide +kernel
def pointBounds28834 : List (Nat × Nat × Nat) := [(3783277568,104723116773740,104723499811889)]
theorem point_links_checked28834 : (cuts28834.take 1).map (fun c => (3783262209-1+2*2^9*c.k,104723066033007+c.lower,104723449071127+c.upper)) = pointBounds28834 := by
 decide +kernel
def cuts28835 : List PrefixCut := [⟨3,10490039,10490045⟩,
⟨119,409402741,409402969⟩,
⟨128,441318189,441318434⟩]
theorem checked28835 : checkPrefixCuts (2^48) 3783393281 9 Manual.Count131072.C028835.packed 128 cuts28835 = true := by
 decide +kernel
def pointBounds28835 : List (Nat × Nat × Nat) := [(3783396352,104723514954906,104723897993280),(3783515136,104723913867608,104724296906204)]
theorem point_links_checked28835 : (cuts28835.take 2).map (fun c => (3783393281-1+2*2^9*c.k,104723504464867+c.lower,104723887503235+c.upper)) = pointBounds28835 := by
 decide +kernel
def cuts28836 : List PrefixCut := [⟨107,375316862,375317071⟩,
⟨128,446956870,446957120⟩]
theorem checked28836 : checkPrefixCuts (2^48) 3783524353 9 Manual.Count131072.C028836.packed 128 cuts28836 = true := by
 decide +kernel
def pointBounds28836 : List (Nat × Nat × Nat) := [(3783633920,104724321099918,104724704138740)]
theorem point_links_checked28836 : (cuts28836.take 1).map (fun c => (3783524353-1+2*2^9*c.k,104723945783056+c.lower,104724328821669+c.upper)) = pointBounds28836 := by
 decide +kernel
def cuts28837 : List PrefixCut := [⟨95,327768330,327768510⟩,
⟨128,444263186,444263431⟩]
theorem checked28837 : checkPrefixCuts (2^48) 3783655425 9 Manual.Count131072.C028837.packed 128 cuts28837 = true := by
 decide +kernel
def pointBounds28837 : List (Nat × Nat × Nat) := [(3783752704,104724720508256,104725103547299)]
theorem point_links_checked28837 : (cuts28837.take 1).map (fun c => (3783655425-1+2*2^9*c.k,104724392739926+c.lower,104724775778789+c.upper)) = pointBounds28837 := by
 decide +kernel
def cuts28838 : List PrefixCut := [⟨83,285578983,285579144⟩,
⟨128,437701665,437701909⟩]
theorem checked28838 : checkPrefixCuts (2^48) 3783786497 9 Manual.Count131072.C028838.packed 128 cuts28838 = true := by
 decide +kernel
def pointBounds28838 : List (Nat × Nat × Nat) := [(3783871488,104725122582095,104725505621364)]
theorem point_links_checked28838 : (cuts28838.take 1).map (fun c => (3783786497-1+2*2^9*c.k,104724837003112+c.lower,104725220042220+c.upper)) = pointBounds28838 := by
 decide +kernel
def cuts28839 : List PrefixCut := [⟨71,243392442,243392575⟩,
⟨128,441108183,441108428⟩]
theorem checked28839 : checkPrefixCuts (2^48) 3783917569 9 Manual.Count131072.C028839.packed 128 cuts28839 = true := by
 decide +kernel
def pointBounds28839 : List (Nat × Nat × Nat) := [(3783990272,104725518097219,104725901136704)]
theorem point_links_checked28839 : (cuts28839.take 1).map (fun c => (3783917569-1+2*2^9*c.k,104725274704777+c.lower,104725657744129+c.upper)) = pointBounds28839 := by
 decide +kernel
def cuts28840 : List PrefixCut := [⟨59,201431862,201431976⟩,
⟨128,440200369,440200618⟩]
theorem checked28840 : checkPrefixCuts (2^48) 3784048641 9 Manual.Count131072.C028840.packed 128 cuts28840 = true := by
 decide +kernel
def pointBounds28840 : List (Nat × Nat × Nat) := [(3784109056,104725917244822,104726300284533)]
theorem point_links_checked28840 : (cuts28840.take 1).map (fun c => (3784048641-1+2*2^9*c.k,104725715812960+c.lower,104726098852557+c.upper)) = pointBounds28840 := by
 decide +kernel
def cuts28841 : List PrefixCut := [⟨47,161259181,161259272⟩,
⟨128,435871072,435871323⟩]
theorem checked28841 : checkPrefixCuts (2^48) 3784179713 9 Manual.Count131072.C028841.packed 128 cuts28841 = true := by
 decide +kernel
def pointBounds28841 : List (Nat × Nat × Nat) := [(3784227840,104726317272510,104726700312447)]
theorem point_links_checked28841 : (cuts28841.take 1).map (fun c => (3784179713-1+2*2^9*c.k,104726156013329+c.lower,104726539053175+c.upper)) = pointBounds28841 := by
 decide +kernel
def cuts28842 : List PrefixCut := [⟨35,120717243,120717310⟩,
⟨128,439946785,439947031⟩]
theorem checked28842 : checkPrefixCuts (2^48) 3784310785 9 Manual.Count131072.C028842.packed 128 cuts28842 = true := by
 decide +kernel
def pointBounds28842 : List (Nat × Nat × Nat) := [(3784346624,104726712601644,104727095641808)]
theorem point_links_checked28842 : (cuts28842.take 1).map (fun c => (3784310785-1+2*2^9*c.k,104726591884401+c.lower,104726974924498+c.upper)) = pointBounds28842 := by
 decide +kernel
def cuts28843 : List PrefixCut := [⟨23,82334933,82334977⟩,
⟨128,449302829,449303081⟩]
theorem checked28843 : checkPrefixCuts (2^48) 3784441857 9 Manual.Count131072.C028843.packed 128 cuts28843 = true := by
 decide +kernel
def pointBounds28843 : List (Nat × Nat × Nat) := [(3784465408,104727114166119,104727497206506)]
theorem point_links_checked28843 : (cuts28843.take 1).map (fun c => (3784441857-1+2*2^9*c.k,104727031831186+c.lower,104727414871529+c.upper)) = pointBounds28843 := by
 decide +kernel
def cuts28844 : List PrefixCut := [⟨11,38377074,38377093⟩,
⟨127,440585657,440585903⟩,
⟨128,443783641,443783889⟩]
theorem checked28844 : checkPrefixCuts (2^48) 3784572929 9 Manual.Count131072.C028844.packed 128 cuts28844 = true := by
 decide +kernel
def pointBounds28844 : List (Nat × Nat × Nat) := [(3784584192,104727519511089,104727902551703),(3784702976,104727921719672,104728304760513)]
theorem point_links_checked28844 : (cuts28844.take 2).map (fun c => (3784572929-1+2*2^9*c.k,104727481134015+c.lower,104727864174610+c.upper)) = pointBounds28844 := by
 decide +kernel
def cuts28845 : List PrefixCut := [⟨115,393271451,393271677⟩,
⟨128,435066980,435067231⟩]
theorem checked28845 : checkPrefixCuts (2^48) 3784704001 9 Manual.Count131072.C028845.packed 128 cuts28845 = true := by
 decide +kernel
def pointBounds28845 : List (Nat × Nat × Nat) := [(3784821760,104728318189107,104728701230176)]
theorem point_links_checked28845 : (cuts28845.take 1).map (fun c => (3784704001-1+2*2^9*c.k,104727924917656+c.lower,104728307958499+c.upper)) = pointBounds28845 := by
 decide +kernel
def cuts28846 : List PrefixCut := [⟨103,351761112,351761316⟩,
⟨128,438547182,438547434⟩]
theorem checked28846 : checkPrefixCuts (2^48) 3784835073 9 Manual.Count131072.C028846.packed 128 cuts28846 = true := by
 decide +kernel
def pointBounds28846 : List (Nat × Nat × Nat) := [(3784940544,104728711745748,104729094787046)]
theorem point_links_checked28846 : (cuts28846.take 1).map (fun c => (3784835073-1+2*2^9*c.k,104728359984636+c.lower,104728743025730+c.upper)) = pointBounds28846 := by
 decide +kernel
def cuts28847 : List PrefixCut := [⟨91,316500208,316500383⟩,
⟨128,443812002,443812244⟩]
theorem checked28847 : checkPrefixCuts (2^48) 3784966145 9 Manual.Count131072.C028847.packed 128 cuts28847 = true := by
 decide +kernel
def pointBounds28847 : List (Nat × Nat × Nat) := [(3785059328,104729115032026,104729498073547)]
theorem point_links_checked28847 : (cuts28847.take 1).map (fun c => (3784966145-1+2*2^9*c.k,104728798531818+c.lower,104729181573164+c.upper)) = pointBounds28847 := by
 decide +kernel
def cuts28848 : List PrefixCut := [⟨79,273507819,273507976⟩,
⟨128,441119545,441119797⟩]
theorem checked28848 : checkPrefixCuts (2^48) 3785097217 9 Manual.Count131072.C028848.packed 128 cuts28848 = true := by
 decide +kernel
def pointBounds28848 : List (Nat × Nat × Nat) := [(3785178112,104729515851639,104729898893384)]
theorem point_links_checked28848 : (cuts28848.take 1).map (fun c => (3785097217-1+2*2^9*c.k,104729242343820+c.lower,104729625385408+c.upper)) = pointBounds28848 := by
 decide +kernel
def cuts28849 : List PrefixCut := [⟨67,232451649,232451778⟩,
⟨128,445937608,445937857⟩]
theorem checked28849 : checkPrefixCuts (2^48) 3785228289 9 Manual.Count131072.C028849.packed 128 cuts28849 = true := by
 decide +kernel
def pointBounds28849 : List (Nat × Nat × Nat) := [(3785296896,104729915915014,104730298956983)]
theorem point_links_checked28849 : (cuts28849.take 1).map (fun c => (3785228289-1+2*2^9*c.k,104729683463365+c.lower,104730066505205+c.upper)) = pointBounds28849 := by
 decide +kernel
def cuts28850 : List PrefixCut := [⟨55,189167449,189167555⟩,
⟨128,439527415,439527664⟩]
theorem checked28850 : checkPrefixCuts (2^48) 3785359361 9 Manual.Count131072.C028850.packed 128 cuts28850 = true := by
 decide +kernel
def pointBounds28850 : List (Nat × Nat × Nat) := [(3785415680,104730318568422,104730701610617)]
theorem point_links_checked28850 : (cuts28850.take 1).map (fun c => (3785359361-1+2*2^9*c.k,104730129400973+c.lower,104730512443062+c.upper)) = pointBounds28850 := by
 decide +kernel
def cuts28851 : List PrefixCut := [⟨43,147298888,147298970⟩,
⟨128,437132887,437133132⟩]
theorem checked28851 : checkPrefixCuts (2^48) 3785490433 9 Manual.Count131072.C028851.packed 128 cuts28851 = true := by
 decide +kernel
def pointBounds28851 : List (Nat × Nat × Nat) := [(3785534464,104730716227276,104731099269696)]
theorem point_links_checked28851 : (cuts28851.take 1).map (fun c => (3785490433-1+2*2^9*c.k,104730568928388+c.lower,104730951970726+c.upper)) = pointBounds28851 := by
 decide +kernel
def cuts28852 : List PrefixCut := [⟨31,109448161,109448221⟩,
⟨128,445147832,445148081⟩]
theorem checked28852 : checkPrefixCuts (2^48) 3785621505 9 Manual.Count131072.C028852.packed 128 cuts28852 = true := by
 decide +kernel
def pointBounds28852 : List (Nat × Nat × Nat) := [(3785653248,104731115509436,104731498552079)]
theorem point_links_checked28852 : (cuts28852.take 1).map (fun c => (3785621505-1+2*2^9*c.k,104731006061275+c.lower,104731389103858+c.upper)) = pointBounds28852 := by
 decide +kernel
def cuts28853 : List PrefixCut := [⟨19,67361929,67361965⟩,
⟨128,444017160,444017401⟩]
theorem checked28853 : checkPrefixCuts (2^48) 3785752577 9 Manual.Count131072.C028853.packed 128 cuts28853 = true := by
 decide +kernel
def pointBounds28853 : List (Nat × Nat × Nat) := [(3785772032,104731518571036,104731901613904)]
theorem point_links_checked28853 : (cuts28853.take 1).map (fun c => (3785752577-1+2*2^9*c.k,104731451209107+c.lower,104731834251939+c.upper)) = pointBounds28853 := by
 decide +kernel
def cuts28854 : List PrefixCut := [⟨7,24758038,24758052⟩,
⟨123,424597443,424597679⟩,
⟨128,441176603,441176849⟩]
theorem checked28854 : checkPrefixCuts (2^48) 3785883649 9 Manual.Count131072.C028854.packed 128 cuts28854 = true := by
 decide +kernel
def pointBounds28854 : List (Nat × Nat × Nat) := [(3785890816,104731919984305,104732303027392),(3786009600,104732319823710,104732702867019)]
theorem point_links_checked28854 : (cuts28854.take 2).map (fun c => (3785883649-1+2*2^9*c.k,104731895226267+c.lower,104732278269340+c.upper)) = pointBounds28854 := by
 decide +kernel
def cuts28855 : List PrefixCut := [⟨111,385106267,385106485⟩,
⟨128,444358080,444358331⟩]
theorem checked28855 : checkPrefixCuts (2^48) 3786014721 9 Manual.Count131072.C028855.packed 128 cuts28855 = true := by
 decide +kernel
def pointBounds28855 : List (Nat × Nat × Nat) := [(3786128384,104732721509137,104733104552674)]
theorem point_links_checked28855 : (cuts28855.take 1).map (fun c => (3786014721-1+2*2^9*c.k,104732336402870+c.lower,104732719446189+c.upper)) = pointBounds28855 := by
 decide +kernel
def cuts28856 : List PrefixCut := [⟨99,337960516,337960707⟩,
⟨128,439213097,439213343⟩]
theorem checked28856 : checkPrefixCuts (2^48) 3786145793 9 Manual.Count131072.C028856.packed 128 cuts28856 = true := by
 decide +kernel
def pointBounds28856 : List (Nat × Nat × Nat) := [(3786247168,104733118721466,104733501765227)]
theorem point_links_checked28856 : (cuts28856.take 1).map (fun c => (3786145793-1+2*2^9*c.k,104732780760950+c.lower,104733163804520+c.upper)) = pointBounds28856 := by
 decide +kernel
def cuts28857 : List PrefixCut := [⟨87,295278248,295278413⟩,
⟨128,439123535,439123781⟩]
theorem checked28857 : checkPrefixCuts (2^48) 3786276865 9 Manual.Count131072.C028857.packed 128 cuts28857 = true := by
 decide +kernel
def pointBounds28857 : List (Nat × Nat × Nat) := [(3786365952,104733515252295,104733898296276)]
theorem point_links_checked28857 : (cuts28857.take 1).map (fun c => (3786276865-1+2*2^9*c.k,104733219974047+c.lower,104733603017863+c.upper)) = pointBounds28857 := by
 decide +kernel
def cuts28858 : List PrefixCut := [⟨75,260478522,260478667⟩,
⟨128,442081855,442082098⟩]
theorem checked28858 : checkPrefixCuts (2^48) 3786407937 9 Manual.Count131072.C028858.packed 128 cuts28858 = true := by
 decide +kernel
def pointBounds28858 : List (Nat × Nat × Nat) := [(3786484736,104733919576104,104734302620311)]
theorem point_links_checked28858 : (cuts28858.take 1).map (fun c => (3786407937-1+2*2^9*c.k,104733659097582+c.lower,104734042141644+c.upper)) = pointBounds28858 := by
 decide +kernel
def cuts28859 : List PrefixCut := [⟨63,213861892,213862014⟩,
⟨128,442735510,442735758⟩]
theorem checked28859 : checkPrefixCuts (2^48) 3786539009 9 Manual.Count131072.C028859.packed 128 cuts28859 = true := by
 decide +kernel
def pointBounds28859 : List (Nat × Nat × Nat) := [(3786603520,104734315041329,104734698085756)]
theorem point_links_checked28859 : (cuts28859.take 1).map (fun c => (3786539009-1+2*2^9*c.k,104734101179437+c.lower,104734484223742+c.upper)) = pointBounds28859 := by
 decide +kernel
def cuts28860 : List PrefixCut := [⟨51,173194909,173195009⟩,
⟨128,437814300,437814547⟩]
theorem checked28860 : checkPrefixCuts (2^48) 3786670081 9 Manual.Count131072.C028860.packed 128 cuts28860 = true := by
 decide +kernel
def pointBounds28860 : List (Nat × Nat × Nat) := [(3786722304,104734717109856,104735100154509)]
theorem point_links_checked28860 : (cuts28860.take 1).map (fun c => (3786670081-1+2*2^9*c.k,104734543914947+c.lower,104734926959500+c.upper)) = pointBounds28860 := by
 decide +kernel
def cuts28861 : List PrefixCut := [⟨39,132753616,132753692⟩,
⟨128,440697963,440698214⟩]
theorem checked28861 : checkPrefixCuts (2^48) 3786801153 9 Manual.Count131072.C028861.packed 128 cuts28861 = true := by
 decide +kernel
def pointBounds28861 : List (Nat × Nat × Nat) := [(3786841088,104735114482863,104735497527739)]
theorem point_links_checked28861 : (cuts28861.take 1).map (fun c => (3786801153-1+2*2^9*c.k,104734981729247+c.lower,104735364774047+c.upper)) = pointBounds28861 := by
 decide +kernel
def cuts28862 : List PrefixCut := [⟨27,92537952,92538006⟩,
⟨128,441723364,441723613⟩]
theorem checked28862 : checkPrefixCuts (2^48) 3786932225 9 Manual.Count131072.C028862.packed 128 cuts28862 = true := by
 decide +kernel
def pointBounds28862 : List (Nat × Nat × Nat) := [(3786959872,104735514965162,104735898010267)]
theorem point_links_checked28862 : (cuts28862.take 1).map (fun c => (3786932225-1+2*2^9*c.k,104735422427210+c.lower,104735805472261+c.upper)) = pointBounds28862 := by
 decide +kernel
def cuts28863 : List PrefixCut := [⟨15,54777692,54777722⟩,
⟨128,439775654,439775901⟩]
theorem checked28863 : checkPrefixCuts (2^48) 3787063297 9 Manual.Count131072.C028863.packed 128 cuts28863 = true := by
 decide +kernel
def pointBounds28863 : List (Nat × Nat × Nat) := [(3787078656,104735918928266,104736301973596)]
theorem point_links_checked28863 : (cuts28863.take 1).map (fun c => (3787063297-1+2*2^9*c.k,104735864150574+c.lower,104736247195874+c.upper)) = pointBounds28863 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000276
