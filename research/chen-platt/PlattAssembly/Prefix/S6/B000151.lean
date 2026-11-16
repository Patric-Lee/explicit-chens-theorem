import PlattAssemblyKernel
import PlattCertificates.Count131072.C054832
import PlattCertificates.Count131072.C054833
import PlattCertificates.Count131072.C054834
import PlattCertificates.Count131072.C054835
import PlattCertificates.Count131072.C054836
import PlattCertificates.Count131072.C054837
import PlattCertificates.Count131072.C054838
import PlattCertificates.Count131072.C054839
import PlattCertificates.Count131072.C054840
import PlattCertificates.Count131072.C054841
import PlattCertificates.Count131072.C054842
import PlattCertificates.Count131072.C054843
import PlattCertificates.Count131072.C054844
import PlattCertificates.Count131072.C054845
import PlattCertificates.Count131072.C054846
import PlattCertificates.Count131072.C054847
import PlattCertificates.Count131072.C054848
import PlattCertificates.Count131072.C054849
import PlattCertificates.Count131072.C054850
import PlattCertificates.Count131072.C054851
import PlattCertificates.Count131072.C054852
import PlattCertificates.Count131072.C054853
import PlattCertificates.Count131072.C054854
import PlattCertificates.Count131072.C054855
import PlattCertificates.Count131072.C054856
import PlattCertificates.Count131072.C054857
import PlattCertificates.Count131072.C054858
import PlattCertificates.Count131072.C054859
import PlattCertificates.Count131072.C054860
import PlattCertificates.Count131072.C054861
import PlattCertificates.Count131072.C054862
import PlattCertificates.Count131072.C054863
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000151
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54832 : List PrefixCut := [⟨64,226246549,226246676⟩]
theorem checked54832 : checkPrefixCuts (2^48) 7190872065 10 Manual.Count131072.C054832.packed 64 cuts54832 = true := by
 decide +kernel
def cuts54833 : List PrefixCut := [⟨41,145296653,145296738⟩,
⟨64,229334659,229334791⟩]
theorem checked54833 : checkPrefixCuts (2^48) 7191003137 10 Manual.Count131072.C054833.packed 64 cuts54833 = true := by
 decide +kernel
def pointBounds54833 : List (Nat × Nat × Nat) := [(7191087104,112802968649600,112803356422889)]
theorem point_links_checked54833 : (cuts54833.take 1).map (fun c => (7191003137-1+2*2^10*c.k,112802823352947+c.lower,112803211126151+c.upper)) = pointBounds54833 := by
 decide +kernel
def cuts54834 : List PrefixCut := [⟨64,225024929,225025056⟩]
theorem checked54834 : checkPrefixCuts (2^48) 7191134209 10 Manual.Count131072.C054834.packed 64 cuts54834 = true := by
 decide +kernel
def cuts54835 : List PrefixCut := [⟨23,82313716,82313763⟩,
⟨64,227878102,227878230⟩]
theorem checked54835 : checkPrefixCuts (2^48) 7191265281 10 Manual.Count131072.C054835.packed 64 cuts54835 = true := by
 decide +kernel
def pointBounds54835 : List (Nat × Nat × Nat) := [(7191312384,112803360026251,112803747799761)]
theorem point_links_checked54835 : (cuts54835.take 1).map (fun c => (7191265281-1+2*2^10*c.k,112803277712535+c.lower,112803665485998+c.upper)) = pointBounds54835 := by
 decide +kernel
def cuts54836 : List PrefixCut := [⟨64,221533231,221533359⟩]
theorem checked54836 : checkPrefixCuts (2^48) 7191396353 10 Manual.Count131072.C054836.packed 64 cuts54836 = true := by
 decide +kernel
def cuts54837 : List PrefixCut := [⟨5,17182357,17182367⟩,
⟨64,226186804,226186935⟩]
theorem checked54837 : checkPrefixCuts (2^48) 7191527425 10 Manual.Count131072.C054837.packed 64 cuts54837 = true := by
 decide +kernel
def pointBounds54837 : List (Nat × Nat × Nat) := [(7191537664,112803744306225,112804132079954)]
theorem point_links_checked54837 : (cuts54837.take 1).map (fun c => (7191527425-1+2*2^10*c.k,112803727123868+c.lower,112804114897587+c.upper)) = pointBounds54837 := by
 decide +kernel
def cuts54838 : List PrefixCut := [⟨51,180742966,180743068⟩,
⟨64,226221831,226221960⟩]
theorem checked54838 : checkPrefixCuts (2^48) 7191658497 10 Manual.Count131072.C054838.packed 64 cuts54838 = true := by
 decide +kernel
def pointBounds54838 : List (Nat × Nat × Nat) := [(7191762944,112804134053638,112804521827590)]
theorem point_links_checked54838 : (cuts54838.take 1).map (fun c => (7191658497-1+2*2^10*c.k,112803953310672+c.lower,112804341084522+c.upper)) = pointBounds54838 := by
 decide +kernel
def cuts54839 : List PrefixCut := [⟨64,227822339,227822466⟩]
theorem checked54839 : checkPrefixCuts (2^48) 7191789569 10 Manual.Count131072.C054839.packed 64 cuts54839 = true := by
 decide +kernel
def cuts54840 : List PrefixCut := [⟨33,117138454,117138519⟩,
⟨64,224843786,224843913⟩]
theorem checked54840 : checkPrefixCuts (2^48) 7191920641 10 Manual.Count131072.C054840.packed 64 cuts54840 = true := by
 decide +kernel
def pointBounds54840 : List (Nat × Nat × Nat) := [(7191988224,112804524493296,112804912267467)]
theorem point_links_checked54840 : (cuts54840.take 1).map (fun c => (7191920641-1+2*2^10*c.k,112804407354842+c.lower,112804795128948+c.upper)) = pointBounds54840 := by
 decide +kernel
def cuts54841 : List PrefixCut := [⟨64,224291772,224291900⟩]
theorem checked54841 : checkPrefixCuts (2^48) 7192051713 10 Manual.Count131072.C054841.packed 64 cuts54841 = true := by
 decide +kernel
def cuts54842 : List PrefixCut := [⟨15,53264288,53264318⟩,
⟨64,230666808,230666939⟩]
theorem checked54842 : checkPrefixCuts (2^48) 7192182785 10 Manual.Count131072.C054842.packed 64 cuts54842 = true := by
 decide +kernel
def pointBounds54842 : List (Nat × Nat × Nat) := [(7192213504,112804909754688,112805297529079)]
theorem point_links_checked54842 : (cuts54842.take 1).map (fun c => (7192182785-1+2*2^10*c.k,112804856490400+c.lower,112805244264761+c.upper)) = pointBounds54842 := by
 decide +kernel
def cuts54843 : List PrefixCut := [⟨61,213912845,213912969⟩,
⟨64,224987998,224988128⟩]
theorem checked54843 : checkPrefixCuts (2^48) 7192313857 10 Manual.Count131072.C054843.packed 64 cuts54843 = true := by
 decide +kernel
def pointBounds54843 : List (Nat × Nat × Nat) := [(7192438784,112805301070053,112805688844669)]
theorem point_links_checked54843 : (cuts54843.take 1).map (fun c => (7192313857-1+2*2^10*c.k,112805087157208+c.lower,112805474931700+c.upper)) = pointBounds54843 := by
 decide +kernel
def cuts54844 : List PrefixCut := [⟨64,227097173,227097301⟩]
theorem checked54844 : checkPrefixCuts (2^48) 7192444929 10 Manual.Count131072.C054844.packed 64 cuts54844 = true := by
 decide +kernel
def cuts54845 : List PrefixCut := [⟨43,151291447,151291533⟩,
⟨64,226662551,226662680⟩]
theorem checked54845 : checkPrefixCuts (2^48) 7192576001 10 Manual.Count131072.C054845.packed 64 cuts54845 = true := by
 decide +kernel
def pointBounds54845 : List (Nat × Nat × Nat) := [(7192664064,112805690533826,112806078308662)]
theorem point_links_checked54845 : (cuts54845.take 1).map (fun c => (7192576001-1+2*2^10*c.k,112805539242379+c.lower,112805927017129+c.upper)) = pointBounds54845 := by
 decide +kernel
def cuts54846 : List PrefixCut := [⟨64,222745144,222745268⟩]
theorem checked54846 : checkPrefixCuts (2^48) 7192707073 10 Manual.Count131072.C054846.packed 64 cuts54846 = true := by
 decide +kernel
def cuts54847 : List PrefixCut := [⟨25,87969911,87969960⟩,
⟨64,223993315,223993443⟩]
theorem checked54847 : checkPrefixCuts (2^48) 7192838145 10 Manual.Count131072.C054847.packed 64 cuts54847 = true := by
 decide +kernel
def pointBounds54847 : List (Nat × Nat × Nat) := [(7192889344,112806076619985,112806464395037)]
theorem point_links_checked54847 : (cuts54847.take 1).map (fun c => (7192838145-1+2*2^10*c.k,112805988650074+c.lower,112806376425077+c.upper)) = pointBounds54847 := by
 decide +kernel
def cuts54848 : List PrefixCut := [⟨64,221954405,221954534⟩]
theorem checked54848 : checkPrefixCuts (2^48) 7192969217 10 Manual.Count131072.C054848.packed 64 cuts54848 = true := by
 decide +kernel
def cuts54849 : List PrefixCut := [⟨7,24770048,24770061⟩,
⟨64,226567785,226567910⟩]
theorem checked54849 : checkPrefixCuts (2^48) 7193100289 10 Manual.Count131072.C054849.packed 64 cuts54849 = true := by
 decide +kernel
def pointBounds54849 : List (Nat × Nat × Nat) := [(7193114624,112806459367842,112806847143115)]
theorem point_links_checked54849 : (cuts54849.take 1).map (fun c => (7193100289-1+2*2^10*c.k,112806434597794+c.lower,112806822373054+c.upper)) = pointBounds54849 := by
 decide +kernel
def cuts54850 : List PrefixCut := [⟨53,187394655,187394761⟩,
⟨64,224841939,224842066⟩]
theorem checked54850 : checkPrefixCuts (2^48) 7193231361 10 Manual.Count131072.C054850.packed 64 cuts54850 = true := by
 decide +kernel
def pointBounds54850 : List (Nat × Nat × Nat) := [(7193339904,112806848560234,112807236335725)]
theorem point_links_checked54850 : (cuts54850.take 1).map (fun c => (7193231361-1+2*2^10*c.k,112806661165579+c.lower,112807048940964+c.upper)) = pointBounds54850 := by
 decide +kernel
def cuts54851 : List PrefixCut := [⟨64,226246475,226246606⟩]
theorem checked54851 : checkPrefixCuts (2^48) 7193362433 10 Manual.Count131072.C054851.packed 64 cuts54851 = true := by
 decide +kernel
def cuts54852 : List PrefixCut := [⟨35,122590839,122590911⟩,
⟨64,225225008,225225138⟩]
theorem checked54852 : checkPrefixCuts (2^48) 7193493505 10 Manual.Count131072.C054852.packed 64 cuts54852 = true := by
 decide +kernel
def pointBounds54852 : List (Nat × Nat × Nat) := [(7193565184,112807234844832,112807622620547)]
theorem point_links_checked54852 : (cuts54852.take 1).map (fun c => (7193493505-1+2*2^10*c.k,112807112253993+c.lower,112807500029636+c.upper)) = pointBounds54852 := by
 decide +kernel
def cuts54853 : List PrefixCut := [⟨64,225886089,225886216⟩]
theorem checked54853 : checkPrefixCuts (2^48) 7193624577 10 Manual.Count131072.C054853.packed 64 cuts54853 = true := by
 decide +kernel
def cuts54854 : List PrefixCut := [⟨17,57791430,57791462⟩,
⟨64,223886462,223886588⟩]
theorem checked54854 : checkPrefixCuts (2^48) 7193755649 10 Manual.Count131072.C054854.packed 64 cuts54854 = true := by
 decide +kernel
def pointBounds54854 : List (Nat × Nat × Nat) := [(7193790464,112807621156520,112808008932452)]
theorem point_links_checked54854 : (cuts54854.take 1).map (fun c => (7193755649-1+2*2^10*c.k,112807563365090+c.lower,112807951140990+c.upper)) = pointBounds54854 := by
 decide +kernel
def cuts54855 : List PrefixCut := [⟨63,223334672,223334798⟩,
⟨64,226425646,226425774⟩]
theorem checked54855 : checkPrefixCuts (2^48) 7193886721 10 Manual.Count131072.C054855.packed 64 cuts54855 = true := by
 decide +kernel
def pointBounds54855 : List (Nat × Nat × Nat) := [(7194015744,112808010586224,112808398362376)]
theorem point_links_checked54855 : (cuts54855.take 1).map (fun c => (7193886721-1+2*2^10*c.k,112807787251552+c.lower,112808175027578+c.upper)) = pointBounds54855 := by
 decide +kernel
def cuts54856 : List PrefixCut := [⟨64,227204020,227204150⟩]
theorem checked54856 : checkPrefixCuts (2^48) 7194017793 10 Manual.Count131072.C054856.packed 64 cuts54856 = true := by
 decide +kernel
def cuts54857 : List PrefixCut := [⟨45,160452772,160452862⟩,
⟨64,229156138,229156266⟩]
theorem checked54857 : checkPrefixCuts (2^48) 7194148865 10 Manual.Count131072.C054857.packed 64 cuts54857 = true := by
 decide +kernel
def pointBounds54857 : List (Nat × Nat × Nat) := [(7194241024,112808401333990,112808789110364)]
theorem point_links_checked54857 : (cuts54857.take 1).map (fun c => (7194148865-1+2*2^10*c.k,112808240881218+c.lower,112808628657502+c.upper)) = pointBounds54857 := by
 decide +kernel
def cuts54858 : List PrefixCut := [⟨64,228017386,228017513⟩]
theorem checked54858 : checkPrefixCuts (2^48) 7194279937 10 Manual.Count131072.C054858.packed 64 cuts54858 = true := by
 decide +kernel
def cuts54859 : List PrefixCut := [⟨27,95736322,95736374⟩,
⟨64,227113365,227113493⟩]
theorem checked54859 : checkPrefixCuts (2^48) 7194411009 10 Manual.Count131072.C054859.packed 64 cuts54859 = true := by
 decide +kernel
def pointBounds54859 : List (Nat × Nat × Nat) := [(7194466304,112808793791064,112809181567655)]
theorem point_links_checked54859 : (cuts54859.take 1).map (fun c => (7194411009-1+2*2^10*c.k,112808698054742+c.lower,112809085831281+c.upper)) = pointBounds54859 := by
 decide +kernel
def cuts54860 : List PrefixCut := [⟨64,226717993,226718121⟩]
theorem checked54860 : checkPrefixCuts (2^48) 7194542081 10 Manual.Count131072.C054860.packed 64 cuts54860 = true := by
 decide +kernel
def cuts54861 : List PrefixCut := [⟨9,31180736,31180754⟩,
⟨64,227965777,227965909⟩]
theorem checked54861 : checkPrefixCuts (2^48) 7194673153 10 Manual.Count131072.C054861.packed 64 cuts54861 = true := by
 decide +kernel
def pointBounds54861 : List (Nat × Nat × Nat) := [(7194691584,112809183066836,112809570843649)]
theorem point_links_checked54861 : (cuts54861.take 1).map (fun c => (7194673153-1+2*2^10*c.k,112809151886100+c.lower,112809539662895+c.upper)) = pointBounds54861 := by
 decide +kernel
def cuts54862 : List PrefixCut := [⟨55,192243849,192243961⟩,
⟨64,225223108,225223239⟩]
theorem checked54862 : checkPrefixCuts (2^48) 7194804225 10 Manual.Count131072.C054862.packed 64 cuts54862 = true := by
 decide +kernel
def pointBounds54862 : List (Nat × Nat × Nat) := [(7194916864,112809572095726,112809959872765)]
theorem point_links_checked54862 : (cuts54862.take 1).map (fun c => (7194804225-1+2*2^10*c.k,112809379851877+c.lower,112809767628804+c.upper)) = pointBounds54862 := by
 decide +kernel
def cuts54863 : List PrefixCut := [⟨64,223771543,223771668⟩]
theorem checked54863 : checkPrefixCuts (2^48) 7194935297 10 Manual.Count131072.C054863.packed 64 cuts54863 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000151
