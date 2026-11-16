import PlattAssemblyKernel
import PlattCertificates.Count131072.C047616
import PlattCertificates.Count131072.C047617
import PlattCertificates.Count131072.C047618
import PlattCertificates.Count131072.C047619
import PlattCertificates.Count131072.C047620
import PlattCertificates.Count131072.C047621
import PlattCertificates.Count131072.C047622
import PlattCertificates.Count131072.C047623
import PlattCertificates.Count131072.C047624
import PlattCertificates.Count131072.C047625
import PlattCertificates.Count131072.C047626
import PlattCertificates.Count131072.C047627
import PlattCertificates.Count131072.C047628
import PlattCertificates.Count131072.C047629
import PlattCertificates.Count131072.C047630
import PlattCertificates.Count131072.C047631
import PlattCertificates.Count131072.C047632
import PlattCertificates.Count131072.C047633
import PlattCertificates.Count131072.C047634
import PlattCertificates.Count131072.C047635
import PlattCertificates.Count131072.C047636
import PlattCertificates.Count131072.C047637
import PlattCertificates.Count131072.C047638
import PlattCertificates.Count131072.C047639
import PlattCertificates.Count131072.C047640
import PlattCertificates.Count131072.C047641
import PlattCertificates.Count131072.C047642
import PlattCertificates.Count131072.C047643
import PlattCertificates.Count131072.C047644
import PlattCertificates.Count131072.C047645
import PlattCertificates.Count131072.C047646
import PlattCertificates.Count131072.C047647
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000238
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts47616 : List PrefixCut := [⟨64,263395860,263396008⟩]
theorem checked47616 : checkPrefixCuts (2^48) 6245056513 10 Manual.Count131072.C047616.packed 64 cuts47616 = true := by
 decide +kernel
def cuts47617 : List PrefixCut := [⟨16,65622749,65622785⟩,
⟨64,260055142,260055294⟩]
theorem checked47617 : checkPrefixCuts (2^48) 6245187585 10 Manual.Count131072.C047617.packed 64 cuts47617 = true := by
 decide +kernel
def pointBounds47617 : List (Nat × Nat × Nat) := [(6245220352,111048573415621,111048960190300)]
theorem point_links_checked47617 : (cuts47617.take 1).map (fun c => (6245187585-1+2*2^10*c.k,111048507792872+c.lower,111048894567515+c.upper)) = pointBounds47617 := by
 decide +kernel
def cuts47618 : List PrefixCut := [⟨48,195691283,195691396⟩,
⟨64,260229969,260230119⟩]
theorem checked47618 : checkPrefixCuts (2^48) 6245318657 10 Manual.Count131072.C047618.packed 64 cuts47618 = true := by
 decide +kernel
def pointBounds47618 : List (Nat × Nat × Nat) := [(6245416960,111048963539297,111049350314205)]
theorem point_links_checked47618 : (cuts47618.take 1).map (fun c => (6245318657-1+2*2^10*c.k,111048767848014+c.lower,111049154622809+c.upper)) = pointBounds47618 := by
 decide +kernel
def cuts47619 : List PrefixCut := [⟨64,259999169,259999327⟩]
theorem checked47619 : checkPrefixCuts (2^48) 6245449729 10 Manual.Count131072.C047619.packed 64 cuts47619 = true := by
 decide +kernel
def cuts47620 : List PrefixCut := [⟨16,67872000,67872039⟩,
⟨64,267249545,267249698⟩]
theorem checked47620 : checkPrefixCuts (2^48) 6245580801 10 Manual.Count131072.C047620.packed 64 cuts47620 = true := by
 decide +kernel
def pointBounds47620 : List (Nat × Nat × Nat) := [(6245613568,111049355949152,111049742724294)]
theorem point_links_checked47620 : (cuts47620.take 1).map (fun c => (6245580801-1+2*2^10*c.k,111049288077152+c.lower,111049674852255+c.upper)) = pointBounds47620 := by
 decide +kernel
def cuts47621 : List PrefixCut := [⟨48,196309894,196310005⟩,
⟨64,261700769,261700917⟩]
theorem checked47621 : checkPrefixCuts (2^48) 6245711873 10 Manual.Count131072.C047621.packed 64 cuts47621 = true := by
 decide +kernel
def pointBounds47621 : List (Nat × Nat × Nat) := [(6245810176,111049751636591,111050138411958)]
theorem point_links_checked47621 : (cuts47621.take 1).map (fun c => (6245711873-1+2*2^10*c.k,111049555326697+c.lower,111049942101953+c.upper)) = pointBounds47621 := by
 decide +kernel
def cuts47622 : List PrefixCut := [⟨64,261920602,261920751⟩]
theorem checked47622 : checkPrefixCuts (2^48) 6245842945 10 Manual.Count131072.C047622.packed 64 cuts47622 = true := by
 decide +kernel
def cuts47623 : List PrefixCut := [⟨16,63406309,63406347⟩,
⟨64,261554571,261554722⟩]
theorem checked47623 : checkPrefixCuts (2^48) 6245974017 10 Manual.Count131072.C047623.packed 64 cuts47623 = true := by
 decide +kernel
def pointBounds47623 : List (Nat × Nat × Nat) := [(6246006784,111050142354377,111050529129968)]
theorem point_links_checked47623 : (cuts47623.take 1).map (fun c => (6245974017-1+2*2^10*c.k,111050078948068+c.lower,111050465723621+c.upper)) = pointBounds47623 := by
 decide +kernel
def cuts47624 : List PrefixCut := [⟨48,197469191,197469302⟩,
⟨64,261549116,261549263⟩]
theorem checked47624 : checkPrefixCuts (2^48) 6246105089 10 Manual.Count131072.C047624.packed 64 cuts47624 = true := by
 decide +kernel
def pointBounds47624 : List (Nat × Nat × Nat) := [(6246203392,111050537971830,111050924747645)]
theorem point_links_checked47624 : (cuts47624.take 1).map (fun c => (6246105089-1+2*2^10*c.k,111050340502639+c.lower,111050727278343+c.upper)) = pointBounds47624 := by
 decide +kernel
def cuts47625 : List PrefixCut := [⟨64,262670171,262670317⟩]
theorem checked47625 : checkPrefixCuts (2^48) 6246236161 10 Manual.Count131072.C047625.packed 64 cuts47625 = true := by
 decide +kernel
def cuts47626 : List PrefixCut := [⟨16,63672686,63672722⟩,
⟨64,261312788,261312935⟩]
theorem checked47626 : checkPrefixCuts (2^48) 6246367233 10 Manual.Count131072.C047626.packed 64 cuts47626 = true := by
 decide +kernel
def pointBounds47626 : List (Nat × Nat × Nat) := [(6246400000,111050928394612,111051315170645)]
theorem point_links_checked47626 : (cuts47626.take 1).map (fun c => (6246367233-1+2*2^10*c.k,111050864721926+c.lower,111051251497923+c.upper)) = pointBounds47626 := by
 decide +kernel
def cuts47627 : List PrefixCut := [⟨48,195654312,195654424⟩,
⟨64,261262258,261262404⟩]
theorem checked47627 : checkPrefixCuts (2^48) 6246498305 10 Manual.Count131072.C047627.packed 64 cuts47627 = true := by
 decide +kernel
def pointBounds47627 : List (Nat × Nat × Nat) := [(6246596608,111051321689026,111051708465282)]
theorem point_links_checked47627 : (cuts47627.take 1).map (fun c => (6246498305-1+2*2^10*c.k,111051126034714+c.lower,111051512810858+c.upper)) = pointBounds47627 := by
 decide +kernel
def cuts47628 : List PrefixCut := [⟨64,258372962,258373107⟩]
theorem checked47628 : checkPrefixCuts (2^48) 6246629377 10 Manual.Count131072.C047628.packed 64 cuts47628 = true := by
 decide +kernel
def cuts47629 : List PrefixCut := [⟨16,64795154,64795191⟩,
⟨64,261251293,261251440⟩]
theorem checked47629 : checkPrefixCuts (2^48) 6246760449 10 Manual.Count131072.C047629.packed 64 cuts47629 = true := by
 decide +kernel
def pointBounds47629 : List (Nat × Nat × Nat) := [(6246793216,111051710465088,111052097241560)]
theorem point_links_checked47629 : (cuts47629.take 1).map (fun c => (6246760449-1+2*2^10*c.k,111051645669934+c.lower,111052032446369+c.upper)) = pointBounds47629 := by
 decide +kernel
def cuts47630 : List PrefixCut := [⟨48,194785891,194786005⟩,
⟨64,262192009,262192164⟩]
theorem checked47630 : checkPrefixCuts (2^48) 6246891521 10 Manual.Count131072.C047630.packed 64 cuts47630 = true := by
 decide +kernel
def pointBounds47630 : List (Nat × Nat × Nat) := [(6246989824,111052101707118,111052488483814)]
theorem point_links_checked47630 : (cuts47630.take 1).map (fun c => (6246891521-1+2*2^10*c.k,111051906921227+c.lower,111052293697809+c.upper)) = pointBounds47630 := by
 decide +kernel
def cuts47631 : List PrefixCut := [⟨64,260474345,260474507⟩]
theorem checked47631 : checkPrefixCuts (2^48) 6247022593 10 Manual.Count131072.C047631.packed 64 cuts47631 = true := by
 decide +kernel
def cuts47632 : List PrefixCut := [⟨16,65061414,65061449⟩,
⟨64,261460146,261460294⟩]
theorem checked47632 : checkPrefixCuts (2^48) 6247153665 10 Manual.Count131072.C047632.packed 64 cuts47632 = true := by
 decide +kernel
def pointBounds47632 : List (Nat × Nat × Nat) := [(6247186432,111052494648995,111052881425929)]
theorem point_links_checked47632 : (cuts47632.take 1).map (fun c => (6247153665-1+2*2^10*c.k,111052429587581+c.lower,111052816364480+c.upper)) = pointBounds47632 := by
 decide +kernel
def cuts47633 : List PrefixCut := [⟨48,197927500,197927615⟩,
⟨64,265149161,265149315⟩]
theorem checked47633 : checkPrefixCuts (2^48) 6247284737 10 Manual.Count131072.C047633.packed 64 cuts47633 = true := by
 decide +kernel
def pointBounds47633 : List (Nat × Nat × Nat) := [(6247383040,111052888975227,111053275752389)]
theorem point_links_checked47633 : (cuts47633.take 1).map (fun c => (6247284737-1+2*2^10*c.k,111052691047727+c.lower,111053077824774+c.upper)) = pointBounds47633 := by
 decide +kernel
def cuts47634 : List PrefixCut := [⟨64,261674436,261674591⟩]
theorem checked47634 : checkPrefixCuts (2^48) 6247415809 10 Manual.Count131072.C047634.packed 64 cuts47634 = true := by
 decide +kernel
def cuts47635 : List PrefixCut := [⟨16,63705718,63705753⟩,
⟨64,260227239,260227387⟩]
theorem checked47635 : checkPrefixCuts (2^48) 6247546881 10 Manual.Count131072.C047635.packed 64 cuts47635 = true := by
 decide +kernel
def pointBounds47635 : List (Nat × Nat × Nat) := [(6247579648,111053281577042,111053668354433)]
theorem point_links_checked47635 : (cuts47635.take 1).map (fun c => (6247546881-1+2*2^10*c.k,111053217871324+c.lower,111053604648680+c.upper)) = pointBounds47635 := by
 decide +kernel
def cuts47636 : List PrefixCut := [⟨48,196788743,196788852⟩,
⟨64,262564508,262564659⟩]
theorem checked47636 : checkPrefixCuts (2^48) 6247677953 10 Manual.Count131072.C047636.packed 64 cuts47636 = true := by
 decide +kernel
def pointBounds47636 : List (Nat × Nat × Nat) := [(6247776256,111053674887306,111054061664919)]
theorem point_links_checked47636 : (cuts47636.take 1).map (fun c => (6247677953-1+2*2^10*c.k,111053478098563+c.lower,111053864876067+c.upper)) = pointBounds47636 := by
 decide +kernel
def cuts47637 : List PrefixCut := [⟨64,259495521,259495667⟩]
theorem checked47637 : checkPrefixCuts (2^48) 6247809025 10 Manual.Count131072.C047637.packed 64 cuts47637 = true := by
 decide +kernel
def cuts47638 : List PrefixCut := [⟨16,65368589,65368625⟩,
⟨64,259940556,259940704⟩]
theorem checked47638 : checkPrefixCuts (2^48) 6247940097 10 Manual.Count131072.C047638.packed 64 cuts47638 = true := by
 decide +kernel
def pointBounds47638 : List (Nat × Nat × Nat) := [(6247972864,111054065527181,111054452305018)]
theorem point_links_checked47638 : (cuts47638.take 1).map (fun c => (6247940097-1+2*2^10*c.k,111054000158592+c.lower,111054386936393+c.upper)) = pointBounds47638 := by
 decide +kernel
def cuts47639 : List PrefixCut := [⟨48,199073882,199073989⟩,
⟨64,263809381,263809525⟩]
theorem checked47639 : checkPrefixCuts (2^48) 6248071169 10 Manual.Count131072.C047639.packed 64 cuts47639 = true := by
 decide +kernel
def pointBounds47639 : List (Nat × Nat × Nat) := [(6248169472,111054459173030,111054845951086)]
theorem point_links_checked47639 : (cuts47639.take 1).map (fun c => (6248071169-1+2*2^10*c.k,111054260099148+c.lower,111054646877097+c.upper)) = pointBounds47639 := by
 decide +kernel
def cuts47640 : List PrefixCut := [⟨64,260019750,260019898⟩]
theorem checked47640 : checkPrefixCuts (2^48) 6248202241 10 Manual.Count131072.C047640.packed 64 cuts47640 = true := by
 decide +kernel
def cuts47641 : List PrefixCut := [⟨16,63382366,63382401⟩,
⟨64,260374683,260374829⟩]
theorem checked47641 : checkPrefixCuts (2^48) 6248333313 10 Manual.Count131072.C047641.packed 64 cuts47641 = true := by
 decide +kernel
def pointBounds47641 : List (Nat × Nat × Nat) := [(6248366080,111054847310645,111055234088921)]
theorem point_links_checked47641 : (cuts47641.take 1).map (fun c => (6248333313-1+2*2^10*c.k,111054783928279+c.lower,111055170706520+c.upper)) = pointBounds47641 := by
 decide +kernel
def cuts47642 : List PrefixCut := [⟨48,198971260,198971370⟩,
⟨64,265099114,265099262⟩]
theorem checked47642 : checkPrefixCuts (2^48) 6248464385 10 Manual.Count131072.C047642.packed 64 cuts47642 = true := by
 decide +kernel
def pointBounds47642 : List (Nat × Nat × Nat) := [(6248562688,111055243274222,111055630052719)]
theorem point_links_checked47642 : (cuts47642.take 1).map (fun c => (6248464385-1+2*2^10*c.k,111055044302962+c.lower,111055431081349+c.upper)) = pointBounds47642 := by
 decide +kernel
def cuts47643 : List PrefixCut := [⟨64,263607041,263607196⟩]
theorem checked47643 : checkPrefixCuts (2^48) 6248595457 10 Manual.Count131072.C047643.packed 64 cuts47643 = true := by
 decide +kernel
def cuts47644 : List PrefixCut := [⟨16,65000000,65000038⟩,
⟨64,260853798,260853953⟩]
theorem checked47644 : checkPrefixCuts (2^48) 6248726529 10 Manual.Count131072.C047644.packed 64 cuts47644 = true := by
 decide +kernel
def pointBounds47644 : List (Nat × Nat × Nat) := [(6248759296,111055638009117,111056024787845)]
theorem point_links_checked47644 : (cuts47644.take 1).map (fun c => (6248726529-1+2*2^10*c.k,111055573009117+c.lower,111055959787807+c.upper)) = pointBounds47644 := by
 decide +kernel
def cuts47645 : List PrefixCut := [⟨48,195400266,195400381⟩,
⟨64,260893355,260893508⟩]
theorem checked47645 : checkPrefixCuts (2^48) 6248857601 10 Manual.Count131072.C047645.packed 64 cuts47645 = true := by
 decide +kernel
def pointBounds47645 : List (Nat × Nat × Nat) := [(6248955904,111056029263181,111056416042141)]
theorem point_links_checked47645 : (cuts47645.take 1).map (fun c => (6248857601-1+2*2^10*c.k,111055833862915+c.lower,111056220641760+c.upper)) = pointBounds47645 := by
 decide +kernel
def cuts47646 : List PrefixCut := [⟨64,261023030,261023181⟩]
theorem checked47646 : checkPrefixCuts (2^48) 6248988673 10 Manual.Count131072.C047646.packed 64 cuts47646 = true := by
 decide +kernel
def cuts47647 : List PrefixCut := [⟨16,65896750,65896789⟩,
⟨64,260747298,260747446⟩]
theorem checked47647 : checkPrefixCuts (2^48) 6249119745 10 Manual.Count131072.C047647.packed 64 cuts47647 = true := by
 decide +kernel
def pointBounds47647 : List (Nat × Nat × Nat) := [(6249152512,111056421676050,111056808455238)]
theorem point_links_checked47647 : (cuts47647.take 1).map (fun c => (6249119745-1+2*2^10*c.k,111056355779300+c.lower,111056742558449+c.upper)) = pointBounds47647 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000238
