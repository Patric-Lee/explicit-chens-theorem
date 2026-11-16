import PlattAssemblyKernel
import PlattCertificates.Count131072.C036720
import PlattCertificates.Count131072.C036721
import PlattCertificates.Count131072.C036722
import PlattCertificates.Count131072.C036723
import PlattCertificates.Count131072.C036724
import PlattCertificates.Count131072.C036725
import PlattCertificates.Count131072.C036726
import PlattCertificates.Count131072.C036727
import PlattCertificates.Count131072.C036728
import PlattCertificates.Count131072.C036729
import PlattCertificates.Count131072.C036730
import PlattCertificates.Count131072.C036731
import PlattCertificates.Count131072.C036732
import PlattCertificates.Count131072.C036733
import PlattCertificates.Count131072.C036734
import PlattCertificates.Count131072.C036735
import PlattCertificates.Count131072.C036736
import PlattCertificates.Count131072.C036737
import PlattCertificates.Count131072.C036738
import PlattCertificates.Count131072.C036739
import PlattCertificates.Count131072.C036740
import PlattCertificates.Count131072.C036741
import PlattCertificates.Count131072.C036742
import PlattCertificates.Count131072.C036743
import PlattCertificates.Count131072.C036744
import PlattCertificates.Count131072.C036745
import PlattCertificates.Count131072.C036746
import PlattCertificates.Count131072.C036747
import PlattCertificates.Count131072.C036748
import PlattCertificates.Count131072.C036749
import PlattCertificates.Count131072.C036750
import PlattCertificates.Count131072.C036751
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000210
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts36720 : List PrefixCut := [⟨64,339677538,339677742⟩]
theorem checked36720 : checkPrefixCuts (2^48) 4816896001 10 Manual.Count131072.C036720.packed 64 cuts36720 = true := by
 decide +kernel
def cuts36721 : List PrefixCut := [⟨7,40202067,40202091⟩,
⟨64,345336278,345336486⟩]
theorem checked36721 : checkPrefixCuts (2^48) 4817027073 10 Manual.Count131072.C036721.packed 64 cuts36721 = true := by
 decide +kernel
def pointBounds36721 : List (Nat × Nat × Nat) := [(4817041408,107789427712001,107789812568841)]
theorem point_links_checked36721 : (cuts36721.take 1).map (fun c => (4817027073-1+2*2^10*c.k,107789387509934+c.lower,107789772366750+c.upper)) = pointBounds36721 := by
 decide +kernel
def cuts36722 : List PrefixCut := [⟨17,91503759,91503815⟩,
⟨64,344684096,344684304⟩]
theorem checked36722 : checkPrefixCuts (2^48) 4817158145 10 Manual.Count131072.C036722.packed 64 cuts36722 = true := by
 decide +kernel
def pointBounds36722 : List (Nat × Nat × Nat) := [(4817192960,107789824349971,107790209207051)]
theorem point_links_checked36722 : (cuts36722.take 1).map (fun c => (4817158145-1+2*2^10*c.k,107789732846212+c.lower,107790117703236+c.upper)) = pointBounds36722 := by
 decide +kernel
def cuts36723 : List PrefixCut := [⟨27,142977727,142977814⟩,
⟨64,335793449,335793656⟩]
theorem checked36723 : checkPrefixCuts (2^48) 4817289217 10 Manual.Count131072.C036723.packed 64 cuts36723 = true := by
 decide +kernel
def pointBounds36723 : List (Nat × Nat × Nat) := [(4817344512,107790220508035,107790605365354)]
theorem point_links_checked36723 : (cuts36723.take 1).map (fun c => (4817289217-1+2*2^10*c.k,107790077530308+c.lower,107790462387540+c.upper)) = pointBounds36723 := by
 decide +kernel
def cuts36724 : List PrefixCut := [⟨37,199765654,199765779⟩,
⟨64,343204674,343204886⟩]
theorem checked36724 : checkPrefixCuts (2^48) 4817420289 10 Manual.Count131072.C036724.packed 64 cuts36724 = true := by
 decide +kernel
def pointBounds36724 : List (Nat × Nat × Nat) := [(4817496064,107790613089411,107790997946975)]
theorem point_links_checked36724 : (cuts36724.take 1).map (fun c => (4817420289-1+2*2^10*c.k,107790413323757+c.lower,107790798181196+c.upper)) = pointBounds36724 := by
 decide +kernel
def cuts36725 : List PrefixCut := [⟨47,251934572,251934724⟩,
⟨64,341500988,341501194⟩]
theorem checked36725 : checkPrefixCuts (2^48) 4817551361 10 Manual.Count131072.C036725.packed 64 cuts36725 = true := by
 decide +kernel
def pointBounds36725 : List (Nat × Nat × Nat) := [(4817647616,107791008463003,107791393320806)]
theorem point_links_checked36725 : (cuts36725.take 1).map (fun c => (4817551361-1+2*2^10*c.k,107790756528431+c.lower,107791141386082+c.upper)) = pointBounds36725 := by
 decide +kernel
def cuts36726 : List PrefixCut := [⟨57,310059689,310059881⟩,
⟨64,347158845,347159059⟩]
theorem checked36726 : checkPrefixCuts (2^48) 4817682433 10 Manual.Count131072.C036726.packed 64 cuts36726 = true := by
 decide +kernel
def pointBounds36726 : List (Nat × Nat × Nat) := [(4817799168,107791408089108,107791792947157)]
theorem point_links_checked36726 : (cuts36726.take 1).map (fun c => (4817682433-1+2*2^10*c.k,107791098029419+c.lower,107791482887276+c.upper)) = pointBounds36726 := by
 decide +kernel
def cuts36727 : List PrefixCut := [⟨64,343819266,343819476⟩]
theorem checked36727 : checkPrefixCuts (2^48) 4817813505 10 Manual.Count131072.C036727.packed 64 cuts36727 = true := by
 decide +kernel
def cuts36728 : List PrefixCut := [⟨3,16241358,16241369⟩,
⟨64,345270492,345270701⟩]
theorem checked36728 : checkPrefixCuts (2^48) 4817944577 10 Manual.Count131072.C036728.packed 64 cuts36728 = true := by
 decide +kernel
def pointBounds36728 : List (Nat × Nat × Nat) := [(4817950720,107791805248888,107792190107180)]
theorem point_links_checked36728 : (cuts36728.take 1).map (fun c => (4817944577-1+2*2^10*c.k,107791789007530+c.lower,107792173865811+c.upper)) = pointBounds36728 := by
 decide +kernel
def cuts36729 : List PrefixCut := [⟨13,70221377,70221417⟩,
⟨64,344560068,344560277⟩]
theorem checked36729 : checkPrefixCuts (2^48) 4818075649 10 Manual.Count131072.C036729.packed 64 cuts36729 = true := by
 decide +kernel
def pointBounds36729 : List (Nat × Nat × Nat) := [(4818102272,107792204499399,107792589357929)]
theorem point_links_checked36729 : (cuts36729.take 1).map (fun c => (4818075649-1+2*2^10*c.k,107792134278022+c.lower,107792519136512+c.upper)) = pointBounds36729 := by
 decide +kernel
def cuts36730 : List PrefixCut := [⟨23,120868344,120868421⟩,
⟨64,341512874,341513089⟩]
theorem checked36730 : checkPrefixCuts (2^48) 4818206721 10 Manual.Count131072.C036730.packed 64 cuts36730 = true := by
 decide +kernel
def pointBounds36730 : List (Nat × Nat × Nat) := [(4818253824,107792599706434,107792984565210)]
theorem point_links_checked36730 : (cuts36730.take 1).map (fun c => (4818206721-1+2*2^10*c.k,107792478838090+c.lower,107792863696789+c.upper)) = pointBounds36730 := by
 decide +kernel
def cuts36731 : List PrefixCut := [⟨33,178230305,178230416⟩,
⟨64,349623494,349623709⟩]
theorem checked36731 : checkPrefixCuts (2^48) 4818337793 10 Manual.Count131072.C036731.packed 64 cuts36731 = true := by
 decide +kernel
def pointBounds36731 : List (Nat × Nat × Nat) := [(4818405376,107792998581269,107793383440294)]
theorem point_links_checked36731 : (cuts36731.take 1).map (fun c => (4818337793-1+2*2^10*c.k,107792820350964+c.lower,107793205209878+c.upper)) = pointBounds36731 := by
 decide +kernel
def cuts36732 : List PrefixCut := [⟨43,229630574,229630715⟩,
⟨64,343480442,343480653⟩]
theorem checked36732 : checkPrefixCuts (2^48) 4818468865 10 Manual.Count131072.C036732.packed 64 cuts36732 = true := by
 decide +kernel
def pointBounds36732 : List (Nat × Nat × Nat) := [(4818556928,107793399605032,107793784464302)]
theorem point_links_checked36732 : (cuts36732.take 1).map (fun c => (4818468865-1+2*2^10*c.k,107793169974458+c.lower,107793554833587+c.upper)) = pointBounds36732 := by
 decide +kernel
def cuts36733 : List PrefixCut := [⟨53,284357322,284357500⟩,
⟨64,343529483,343529696⟩]
theorem checked36733 : checkPrefixCuts (2^48) 4818599937 10 Manual.Count131072.C036733.packed 64 cuts36733 = true := by
 decide +kernel
def pointBounds36733 : List (Nat × Nat × Nat) := [(4818708480,107793797812222,107794182671740)]
theorem point_links_checked36733 : (cuts36733.take 1).map (fun c => (4818599937-1+2*2^10*c.k,107793513454900+c.lower,107793898314240+c.upper)) = pointBounds36733 := by
 decide +kernel
def cuts36734 : List PrefixCut := [⟨63,335751498,335751709⟩,
⟨64,341592606,341592821⟩]
theorem checked36734 : checkPrefixCuts (2^48) 4818731009 10 Manual.Count131072.C036734.packed 64 cuts36734 = true := by
 decide +kernel
def pointBounds36734 : List (Nat × Nat × Nat) := [(4818860032,107794192735881,107794577595645)]
theorem point_links_checked36734 : (cuts36734.take 1).map (fun c => (4818731009-1+2*2^10*c.k,107793856984383+c.lower,107794241843936+c.upper)) = pointBounds36734 := by
 decide +kernel
def cuts36735 : List PrefixCut := [⟨64,336793674,336793885⟩]
theorem checked36735 : checkPrefixCuts (2^48) 4818862081 10 Manual.Count131072.C036735.packed 64 cuts36735 = true := by
 decide +kernel
def cuts36736 : List PrefixCut := [⟨9,50699335,50699364⟩,
⟨64,344961753,344961962⟩]
theorem checked36736 : checkPrefixCuts (2^48) 4818993153 10 Manual.Count131072.C036736.packed 64 cuts36736 = true := by
 decide +kernel
def pointBounds36736 : List (Nat × Nat × Nat) := [(4819011584,107794586069998,107794970930006)]
theorem point_links_checked36736 : (cuts36736.take 1).map (fun c => (4818993153-1+2*2^10*c.k,107794535370663+c.lower,107794920230642+c.upper)) = pointBounds36736 := by
 decide +kernel
def cuts36737 : List PrefixCut := [⟨19,101103654,101103717⟩,
⟨64,339286827,339287039⟩]
theorem checked36737 : checkPrefixCuts (2^48) 4819124225 10 Manual.Count131072.C036737.packed 64 cuts36737 = true := by
 decide +kernel
def pointBounds36737 : List (Nat × Nat × Nat) := [(4819163136,107794981436070,107795366296321)]
theorem point_links_checked36737 : (cuts36737.take 1).map (fun c => (4819124225-1+2*2^10*c.k,107794880332416+c.lower,107795265192604+c.upper)) = pointBounds36737 := by
 decide +kernel
def cuts36738 : List PrefixCut := [⟨29,157812860,157812957⟩,
⟨64,345819038,345819246⟩]
theorem checked36738 : checkPrefixCuts (2^48) 4819255297 10 Manual.Count131072.C036738.packed 64 cuts36738 = true := by
 decide +kernel
def pointBounds36738 : List (Nat × Nat × Nat) := [(4819314688,107795377432103,107795762292600)]
theorem point_links_checked36738 : (cuts36738.take 1).map (fun c => (4819255297-1+2*2^10*c.k,107795219619243+c.lower,107795604479643+c.upper)) = pointBounds36738 := by
 decide +kernel
def cuts36739 : List PrefixCut := [⟨39,205524490,205524617⟩,
⟨64,337282631,337282840⟩]
theorem checked36739 : checkPrefixCuts (2^48) 4819386369 10 Manual.Count131072.C036739.packed 64 cuts36739 = true := by
 decide +kernel
def pointBounds36739 : List (Nat × Nat × Nat) := [(4819466240,107795770962771,107796155823506)]
theorem point_links_checked36739 : (cuts36739.take 1).map (fun c => (4819386369-1+2*2^10*c.k,107795565438281+c.lower,107795950298889+c.upper)) = pointBounds36739 := by
 decide +kernel
def cuts36740 : List PrefixCut := [⟨49,259365576,259365735⟩,
⟨64,338032703,338032912⟩]
theorem checked36740 : checkPrefixCuts (2^48) 4819517441 10 Manual.Count131072.C036740.packed 64 cuts36740 = true := by
 decide +kernel
def pointBounds36740 : List (Nat × Nat × Nat) := [(4819617792,107796162086488,107796546947464)]
theorem point_links_checked36740 : (cuts36740.take 1).map (fun c => (4819517441-1+2*2^10*c.k,107795902720912+c.lower,107796287581729+c.upper)) = pointBounds36740 := by
 decide +kernel
def cuts36741 : List PrefixCut := [⟨59,316123592,316123783⟩,
⟨64,343513199,343513406⟩]
theorem checked36741 : checkPrefixCuts (2^48) 4819648513 10 Manual.Count131072.C036741.packed 64 cuts36741 = true := by
 decide +kernel
def pointBounds36741 : List (Nat × Nat × Nat) := [(4819769344,107796556877207,107796941738424)]
theorem point_links_checked36741 : (cuts36741.take 1).map (fun c => (4819648513-1+2*2^10*c.k,107796240753615+c.lower,107796625614641+c.upper)) = pointBounds36741 := by
 decide +kernel
def cuts36742 : List PrefixCut := [⟨64,348117384,348117593⟩]
theorem checked36742 : checkPrefixCuts (2^48) 4819779585 10 Manual.Count131072.C036742.packed 64 cuts36742 = true := by
 decide +kernel
def cuts36743 : List PrefixCut := [⟨5,26804818,26804836⟩,
⟨64,345304846,345305056⟩]
theorem checked36743 : checkPrefixCuts (2^48) 4819910657 10 Manual.Count131072.C036743.packed 64 cuts36743 = true := by
 decide +kernel
def pointBounds36743 : List (Nat × Nat × Nat) := [(4819920896,107796959189016,107797344050476)]
theorem point_links_checked36743 : (cuts36743.take 1).map (fun c => (4819910657-1+2*2^10*c.k,107796932384198+c.lower,107797317245640+c.upper)) = pointBounds36743 := by
 decide +kernel
def cuts36744 : List PrefixCut := [⟨15,81229656,81229704⟩,
⟨64,342200466,342200674⟩]
theorem checked36744 : checkPrefixCuts (2^48) 4820041729 10 Manual.Count131072.C036744.packed 64 cuts36744 = true := by
 decide +kernel
def pointBounds36744 : List (Nat × Nat × Nat) := [(4820072448,107797358918700,107797743780400)]
theorem point_links_checked36744 : (cuts36744.take 1).map (fun c => (4820041729-1+2*2^10*c.k,107797277689044+c.lower,107797662550696+c.upper)) = pointBounds36744 := by
 decide +kernel
def cuts36745 : List PrefixCut := [⟨25,131972416,131972494⟩,
⟨64,341256798,341257005⟩]
theorem checked36745 : checkPrefixCuts (2^48) 4820172801 10 Manual.Count131072.C036745.packed 64 cuts36745 = true := by
 decide +kernel
def pointBounds36745 : List (Nat × Nat × Nat) := [(4820224000,107797751861926,107798136723864)]
theorem point_links_checked36745 : (cuts36745.take 1).map (fun c => (4820172801-1+2*2^10*c.k,107797619889510+c.lower,107798004751370+c.upper)) = pointBounds36745 := by
 decide +kernel
def cuts36746 : List PrefixCut := [⟨35,187617258,187617372⟩,
⟨64,341481156,341481360⟩]
theorem checked36746 : checkPrefixCuts (2^48) 4820303873 10 Manual.Count131072.C036746.packed 64 cuts36746 = true := by
 decide +kernel
def pointBounds36746 : List (Nat × Nat × Nat) := [(4820375552,107798148763566,107798533625747)]
theorem point_links_checked36746 : (cuts36746.take 1).map (fun c => (4820303873-1+2*2^10*c.k,107797961146308+c.lower,107798346008375+c.upper)) = pointBounds36746 := by
 decide +kernel
def cuts36747 : List PrefixCut := [⟨45,238295520,238295669⟩,
⟨64,342581242,342581451⟩]
theorem checked36747 : checkPrefixCuts (2^48) 4820434945 10 Manual.Count131072.C036747.packed 64 cuts36747 = true := by
 decide +kernel
def pointBounds36747 : List (Nat × Nat × Nat) := [(4820527104,107798540922984,107798925785404)]
theorem point_links_checked36747 : (cuts36747.take 1).map (fun c => (4820434945-1+2*2^10*c.k,107798302627464+c.lower,107798687489735+c.upper)) = pointBounds36747 := by
 decide +kernel
def cuts36748 : List PrefixCut := [⟨55,294401092,294401274⟩,
⟨64,343214253,343214464⟩]
theorem checked36748 : checkPrefixCuts (2^48) 4820566017 10 Manual.Count131072.C036748.packed 64 cuts36748 = true := by
 decide +kernel
def pointBounds36748 : List (Nat × Nat × Nat) := [(4820678656,107798939609798,107799324472460)]
theorem point_links_checked36748 : (cuts36748.take 1).map (fun c => (4820566017-1+2*2^10*c.k,107798645208706+c.lower,107799030071186+c.upper)) = pointBounds36748 := by
 decide +kernel
def cuts36749 : List PrefixCut := [⟨64,343204897,343205105⟩]
theorem checked36749 : checkPrefixCuts (2^48) 4820697089 10 Manual.Count131072.C036749.packed 64 cuts36749 = true := by
 decide +kernel
def cuts36750 : List PrefixCut := [⟨1,6130660,6130663⟩,
⟨64,345063943,345064153⟩]
theorem checked36750 : checkPrefixCuts (2^48) 4820828161 10 Manual.Count131072.C036750.packed 64 cuts36750 = true := by
 decide +kernel
def pointBounds36750 : List (Nat × Nat × Nat) := [(4820830208,107799337758516,107799722621418)]
theorem point_links_checked36750 : (cuts36750.take 1).map (fun c => (4820828161-1+2*2^10*c.k,107799331627856+c.lower,107799716490755+c.upper)) = pointBounds36750 := by
 decide +kernel
def cuts36751 : List PrefixCut := [⟨11,56050099,56050135⟩,
⟨64,344879377,344879588⟩]
theorem checked36751 : checkPrefixCuts (2^48) 4820959233 10 Manual.Count131072.C036751.packed 64 cuts36751 = true := by
 decide +kernel
def pointBounds36751 : List (Nat × Nat × Nat) := [(4820981760,107799732741898,107800117605043)]
theorem point_links_checked36751 : (cuts36751.take 1).map (fun c => (4820959233-1+2*2^10*c.k,107799676691799+c.lower,107800061554908+c.upper)) = pointBounds36751 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000210
