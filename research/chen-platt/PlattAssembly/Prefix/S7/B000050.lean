import PlattAssemblyKernel
import PlattCertificates.Count131072.C061600
import PlattCertificates.Count131072.C061601
import PlattCertificates.Count131072.C061602
import PlattCertificates.Count131072.C061603
import PlattCertificates.Count131072.C061604
import PlattCertificates.Count131072.C061605
import PlattCertificates.Count131072.C061606
import PlattCertificates.Count131072.C061607
import PlattCertificates.Count131072.C061608
import PlattCertificates.Count131072.C061609
import PlattCertificates.Count131072.C061610
import PlattCertificates.Count131072.C061611
import PlattCertificates.Count131072.C061612
import PlattCertificates.Count131072.C061613
import PlattCertificates.Count131072.C061614
import PlattCertificates.Count131072.C061615
import PlattCertificates.Count131072.C061616
import PlattCertificates.Count131072.C061617
import PlattCertificates.Count131072.C061618
import PlattCertificates.Count131072.C061619
import PlattCertificates.Count131072.C061620
import PlattCertificates.Count131072.C061621
import PlattCertificates.Count131072.C061622
import PlattCertificates.Count131072.C061623
import PlattCertificates.Count131072.C061624
import PlattCertificates.Count131072.C061625
import PlattCertificates.Count131072.C061626
import PlattCertificates.Count131072.C061627
import PlattCertificates.Count131072.C061628
import PlattCertificates.Count131072.C061629
import PlattCertificates.Count131072.C061630
import PlattCertificates.Count131072.C061631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61600 : List PrefixCut := [⟨36,114743304,114743369⟩,
⟨64,202585846,202585962⟩]
theorem checked61600 : checkPrefixCuts (2^48) 8077967361 10 Manual.Count131072.C061600.packed 64 cuts61600 = true := by
 decide +kernel
def pointBounds61600 : List (Nat × Nat × Nat) := [(8078041088,114241702888520,114242091481619)]
theorem point_links_checked61600 : (cuts61600.take 1).map (fun c => (8077967361-1+2*2^10*c.k,114241588145216+c.lower,114241976738250+c.upper)) = pointBounds61600 := by
 decide +kernel
def cuts61601 : List PrefixCut := [⟨64,201606912,201607029⟩]
theorem checked61601 : checkPrefixCuts (2^48) 8078098433 10 Manual.Count131072.C061601.packed 64 cuts61601 = true := by
 decide +kernel
def cuts61602 : List PrefixCut := [⟨32,102230814,102230870⟩,
⟨64,200976478,200976592⟩]
theorem checked61602 : checkPrefixCuts (2^48) 8078229505 10 Manual.Count131072.C061602.packed 64 cuts61602 = true := by
 decide +kernel
def pointBounds61602 : List (Nat × Nat × Nat) := [(8078295040,114242094568788,114242483162111)]
theorem point_links_checked61602 : (cuts61602.take 1).map (fun c => (8078229505-1+2*2^10*c.k,114241992337974+c.lower,114242380931241+c.upper)) = pointBounds61602 := by
 decide +kernel
def cuts61603 : List PrefixCut := [⟨64,202854740,202854849⟩]
theorem checked61603 : checkPrefixCuts (2^48) 8078360577 10 Manual.Count131072.C061603.packed 64 cuts61603 = true := by
 decide +kernel
def cuts61604 : List PrefixCut := [⟨28,89126814,89126863⟩,
⟨64,201248694,201248804⟩]
theorem checked61604 : checkPrefixCuts (2^48) 8078491649 10 Manual.Count131072.C061604.packed 64 cuts61604 = true := by
 decide +kernel
def pointBounds61604 : List (Nat × Nat × Nat) := [(8078548992,114242485296006,114242873889545)]
theorem point_links_checked61604 : (cuts61604.take 1).map (fun c => (8078491649-1+2*2^10*c.k,114242396169192+c.lower,114242784762682+c.upper)) = pointBounds61604 := by
 decide +kernel
def cuts61605 : List PrefixCut := [⟨64,196297902,196298020⟩]
theorem checked61605 : checkPrefixCuts (2^48) 8078622721 10 Manual.Count131072.C061605.packed 64 cuts61605 = true := by
 decide +kernel
def cuts61606 : List PrefixCut := [⟨24,73027301,73027342⟩,
⟨64,197270266,197270381⟩]
theorem checked61606 : checkPrefixCuts (2^48) 8078753793 10 Manual.Count131072.C061606.packed 64 cuts61606 = true := by
 decide +kernel
def pointBounds61606 : List (Nat × Nat × Nat) := [(8078802944,114242866743089,114243255336848)]
theorem point_links_checked61606 : (cuts61606.take 1).map (fun c => (8078753793-1+2*2^10*c.k,114242793715788+c.lower,114243182309506+c.upper)) = pointBounds61606 := by
 decide +kernel
def cuts61607 : List PrefixCut := [⟨64,202109910,202110022⟩]
theorem checked61607 : checkPrefixCuts (2^48) 8078884865 10 Manual.Count131072.C061607.packed 64 cuts61607 = true := by
 decide +kernel
def cuts61608 : List PrefixCut := [⟨20,60517350,60517388⟩,
⟨64,196288345,196288462⟩]
theorem checked61608 : checkPrefixCuts (2^48) 8079015937 10 Manual.Count131072.C061608.packed 64 cuts61608 = true := by
 decide +kernel
def pointBounds61608 : List (Nat × Nat × Nat) := [(8079056896,114243253613314,114243642207297)]
theorem point_links_checked61608 : (cuts61608.take 1).map (fun c => (8079015937-1+2*2^10*c.k,114243193095964+c.lower,114243581689909+c.upper)) = pointBounds61608 := by
 decide +kernel
def cuts61609 : List PrefixCut := [⟨64,202904647,202904766⟩]
theorem checked61609 : checkPrefixCuts (2^48) 8079147009 10 Manual.Count131072.C061609.packed 64 cuts61609 = true := by
 decide +kernel
def cuts61610 : List PrefixCut := [⟨16,49192730,49192758⟩,
⟨64,201577472,201577590⟩]
theorem checked61610 : checkPrefixCuts (2^48) 8079278081 10 Manual.Count131072.C061610.packed 64 cuts61610 = true := by
 decide +kernel
def pointBounds61610 : List (Nat × Nat × Nat) := [(8079310848,114243641481686,114244030075895)]
theorem point_links_checked61610 : (cuts61610.take 1).map (fun c => (8079278081-1+2*2^10*c.k,114243592288956+c.lower,114243980883137+c.upper)) = pointBounds61610 := by
 decide +kernel
def cuts61611 : List PrefixCut := [⟨64,201469696,201469814⟩]
theorem checked61611 : checkPrefixCuts (2^48) 8079409153 10 Manual.Count131072.C061611.packed 64 cuts61611 = true := by
 decide +kernel
def cuts61612 : List PrefixCut := [⟨12,37241749,37241770⟩,
⟨64,198609728,198609845⟩]
theorem checked61612 : checkPrefixCuts (2^48) 8079540225 10 Manual.Count131072.C061612.packed 64 cuts61612 = true := by
 decide +kernel
def pointBounds61612 : List (Nat × Nat × Nat) := [(8079564800,114244032577873,114244421172311)]
theorem point_links_checked61612 : (cuts61612.take 1).map (fun c => (8079540225-1+2*2^10*c.k,114243995336124+c.lower,114244383930541+c.upper)) = pointBounds61612 := by
 decide +kernel
def cuts61613 : List PrefixCut := [⟨64,201672197,201672306⟩]
theorem checked61613 : checkPrefixCuts (2^48) 8079671297 10 Manual.Count131072.C061613.packed 64 cuts61613 = true := by
 decide +kernel
def cuts61614 : List PrefixCut := [⟨8,26197286,26197302⟩,
⟨64,199613557,199613676⟩]
theorem checked61614 : checkPrefixCuts (2^48) 8079802369 10 Manual.Count131072.C061614.packed 64 cuts61614 = true := by
 decide +kernel
def pointBounds61614 : List (Nat × Nat × Nat) := [(8079818752,114244421815335,114244810409994)]
theorem point_links_checked61614 : (cuts61614.take 1).map (fun c => (8079802369-1+2*2^10*c.k,114244395618049+c.lower,114244784212692+c.upper)) = pointBounds61614 := by
 decide +kernel
def cuts61615 : List PrefixCut := [⟨64,201003755,201003868⟩]
theorem checked61615 : checkPrefixCuts (2^48) 8079933441 10 Manual.Count131072.C061615.packed 64 cuts61615 = true := by
 decide +kernel
def cuts61616 : List PrefixCut := [⟨4,12819540,12819548⟩,
⟨64,202219735,202219855⟩]
theorem checked61616 : checkPrefixCuts (2^48) 8080064513 10 Manual.Count131072.C061616.packed 64 cuts61616 = true := by
 decide +kernel
def pointBounds61616 : List (Nat × Nat × Nat) := [(8080072704,114244809054901,114245197649784)]
theorem point_links_checked61616 : (cuts61616.take 1).map (fun c => (8080064513-1+2*2^10*c.k,114244796235361+c.lower,114245184830236+c.upper)) = pointBounds61616 := by
 decide +kernel
def cuts61617 : List PrefixCut := [⟨64,201937781,201937897⟩]
theorem checked61617 : checkPrefixCuts (2^48) 8080195585 10 Manual.Count131072.C061617.packed 64 cuts61617 = true := by
 decide +kernel
def pointBounds61617 : List (Nat × Nat × Nat) := [(8080326656,114245200392877,114245588987988)]
theorem point_links_checked61617 : (cuts61617.take 1).map (fun c => (8080195585-1+2*2^10*c.k,114244998455096+c.lower,114245387050091+c.upper)) = pointBounds61617 := by
 decide +kernel
def cuts61618 : List PrefixCut := [⟨64,200471460,200471578⟩]
theorem checked61618 : checkPrefixCuts (2^48) 8080326657 10 Manual.Count131072.C061618.packed 64 cuts61618 = true := by
 decide +kernel
def cuts61619 : List PrefixCut := [⟨60,188555152,188555256⟩,
⟨64,201861542,201861654⟩]
theorem checked61619 : checkPrefixCuts (2^48) 8080457729 10 Manual.Count131072.C061619.packed 64 cuts61619 = true := by
 decide +kernel
def pointBounds61619 : List (Nat × Nat × Nat) := [(8080580608,114245589419489,114245978014822)]
theorem point_links_checked61619 : (cuts61619.take 1).map (fun c => (8080457729-1+2*2^10*c.k,114245400864337+c.lower,114245789459566+c.upper)) = pointBounds61619 := by
 decide +kernel
def cuts61620 : List PrefixCut := [⟨64,201544775,201544891⟩]
theorem checked61620 : checkPrefixCuts (2^48) 8080588801 10 Manual.Count131072.C061620.packed 64 cuts61620 = true := by
 decide +kernel
def cuts61621 : List PrefixCut := [⟨56,174929576,174929674⟩,
⟨64,200357206,200357319⟩]
theorem checked61621 : checkPrefixCuts (2^48) 8080719873 10 Manual.Count131072.C061621.packed 64 cuts61621 = true := by
 decide +kernel
def pointBounds61621 : List (Nat × Nat × Nat) := [(8080834560,114245979200230,114246367795785)]
theorem point_links_checked61621 : (cuts61621.take 1).map (fun c => (8080719873-1+2*2^10*c.k,114245804270654+c.lower,114246192866111+c.upper)) = pointBounds61621 := by
 decide +kernel
def cuts61622 : List PrefixCut := [⟨64,199866305,199866421⟩]
theorem checked61622 : checkPrefixCuts (2^48) 8080850945 10 Manual.Count131072.C061622.packed 64 cuts61622 = true := by
 decide +kernel
def cuts61623 : List PrefixCut := [⟨52,163499238,163499334⟩,
⟨64,200629357,200629477⟩]
theorem checked61623 : checkPrefixCuts (2^48) 8080982017 10 Manual.Count131072.C061623.packed 64 cuts61623 = true := by
 decide +kernel
def pointBounds61623 : List (Nat × Nat × Nat) := [(8081088512,114246367993403,114246756589185)]
theorem point_links_checked61623 : (cuts61623.take 1).map (fun c => (8080982017-1+2*2^10*c.k,114246204494165+c.lower,114246593089851+c.upper)) = pointBounds61623 := by
 decide +kernel
def cuts61624 : List PrefixCut := [⟨64,199232864,199232977⟩]
theorem checked61624 : checkPrefixCuts (2^48) 8081113089 10 Manual.Count131072.C061624.packed 64 cuts61624 = true := by
 decide +kernel
def cuts61625 : List PrefixCut := [⟨48,148482111,148482197⟩,
⟨64,200448688,200448802⟩]
theorem checked61625 : checkPrefixCuts (2^48) 8081244161 10 Manual.Count131072.C061625.packed 64 cuts61625 = true := by
 decide +kernel
def pointBounds61625 : List (Nat × Nat × Nat) := [(8081342464,114246752838497,114247141434502)]
theorem point_links_checked61625 : (cuts61625.take 1).map (fun c => (8081244161-1+2*2^10*c.k,114246604356386+c.lower,114246992952305+c.upper)) = pointBounds61625 := by
 decide +kernel
def cuts61626 : List PrefixCut := [⟨64,201176875,201176991⟩]
theorem checked61626 : checkPrefixCuts (2^48) 8081375233 10 Manual.Count131072.C061626.packed 64 cuts61626 = true := by
 decide +kernel
def cuts61627 : List PrefixCut := [⟨44,136252279,136252360⟩,
⟨64,198422102,198422219⟩]
theorem checked61627 : checkPrefixCuts (2^48) 8081506305 10 Manual.Count131072.C061627.packed 64 cuts61627 = true := by
 decide +kernel
def pointBounds61627 : List (Nat × Nat × Nat) := [(8081596416,114247142234228,114247530830458)]
theorem point_links_checked61627 : (cuts61627.take 1).map (fun c => (8081506305-1+2*2^10*c.k,114247005981949+c.lower,114247394578098+c.upper)) = pointBounds61627 := by
 decide +kernel
def cuts61628 : List PrefixCut := [⟨64,197791970,197792081⟩]
theorem checked61628 : checkPrefixCuts (2^48) 8081637377 10 Manual.Count131072.C061628.packed 64 cuts61628 = true := by
 decide +kernel
def cuts61629 : List PrefixCut := [⟨40,126147740,126147811⟩,
⟨64,201306396,201306510⟩]
theorem checked61629 : checkPrefixCuts (2^48) 8081768449 10 Manual.Count131072.C061629.packed 64 cuts61629 = true := by
 decide +kernel
def pointBounds61629 : List (Nat × Nat × Nat) := [(8081850368,114247528343761,114247916940209)]
theorem point_links_checked61629 : (cuts61629.take 1).map (fun c => (8081768449-1+2*2^10*c.k,114247402196021+c.lower,114247790792398+c.upper)) = pointBounds61629 := by
 decide +kernel
def cuts61630 : List PrefixCut := [⟨64,197715899,197716012⟩]
theorem checked61630 : checkPrefixCuts (2^48) 8081899521 10 Manual.Count131072.C061630.packed 64 cuts61630 = true := by
 decide +kernel
def cuts61631 : List PrefixCut := [⟨36,111551173,111551236⟩,
⟨64,198896808,198896919⟩]
theorem checked61631 : checkPrefixCuts (2^48) 8082030593 10 Manual.Count131072.C061631.packed 64 cuts61631 = true := by
 decide +kernel
def pointBounds61631 : List (Nat × Nat × Nat) := [(8082104320,114247912769489,114248301366156)]
theorem point_links_checked61631 : (cuts61631.take 1).map (fun c => (8082030593-1+2*2^10*c.k,114247801218316+c.lower,114248189814920+c.upper)) = pointBounds61631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000050
