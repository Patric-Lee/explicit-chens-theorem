import PlattAssemblyKernel
import PlattCertificates.Count131072.C023776
import PlattCertificates.Count131072.C023777
import PlattCertificates.Count131072.C023778
import PlattCertificates.Count131072.C023779
import PlattCertificates.Count131072.C023780
import PlattCertificates.Count131072.C023781
import PlattCertificates.Count131072.C023782
import PlattCertificates.Count131072.C023783
import PlattCertificates.Count131072.C023784
import PlattCertificates.Count131072.C023785
import PlattCertificates.Count131072.C023786
import PlattCertificates.Count131072.C023787
import PlattCertificates.Count131072.C023788
import PlattCertificates.Count131072.C023789
import PlattCertificates.Count131072.C023790
import PlattCertificates.Count131072.C023791
import PlattCertificates.Count131072.C023792
import PlattCertificates.Count131072.C023793
import PlattCertificates.Count131072.C023794
import PlattCertificates.Count131072.C023795
import PlattCertificates.Count131072.C023796
import PlattCertificates.Count131072.C023797
import PlattCertificates.Count131072.C023798
import PlattCertificates.Count131072.C023799
import PlattCertificates.Count131072.C023800
import PlattCertificates.Count131072.C023801
import PlattCertificates.Count131072.C023802
import PlattCertificates.Count131072.C023803
import PlattCertificates.Count131072.C023804
import PlattCertificates.Count131072.C023805
import PlattCertificates.Count131072.C023806
import PlattCertificates.Count131072.C023807
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000118
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23776 : List PrefixCut := [⟨95,405025960,405026188⟩,
⟨128,545564324,545564629⟩]
theorem checked23776 : checkPrefixCuts (2^48) 3120300033 9 Manual.Count131072.C023776.packed 128 cuts23776 = true := by
 decide +kernel
def pointBounds23776 : List (Nat × Nat × Nat) := [(3120397312,102253629671066,102254011324484)]
theorem point_links_checked23776 : (cuts23776.take 1).map (fun c => (3120300033-1+2*2^9*c.k,102253224645106+c.lower,102253606298296+c.upper)) = pointBounds23776 := by
 decide +kernel
def cuts23777 : List PrefixCut := [⟨63,264023927,264024083⟩,
⟨128,535889824,535890129⟩]
theorem checked23777 : checkPrefixCuts (2^48) 3120431105 9 Manual.Count131072.C023777.packed 128 cuts23777 = true := by
 decide +kernel
def pointBounds23777 : List (Nat × Nat × Nat) := [(3120495616,102254034233357,102254415887008)]
theorem point_links_checked23777 : (cuts23777.take 1).map (fun c => (3120431105-1+2*2^9*c.k,102253770209430+c.lower,102254151862925+c.upper)) = pointBounds23777 := by
 decide +kernel
def cuts23778 : List PrefixCut := [⟨31,131060013,131060087⟩,
⟨127,536047769,536048072⟩,
⟨128,539294835,539295140⟩]
theorem checked23778 : checkPrefixCuts (2^48) 3120562177 9 Manual.Count131072.C023778.packed 128 cuts23778 = true := by
 decide +kernel
def pointBounds23778 : List (Nat × Nat × Nat) := [(3120593920,102254437159267,102254818813141),(3120692224,102254842147023,102255223801126)]
theorem point_links_checked23778 : (cuts23778.take 2).map (fun c => (3120562177-1+2*2^9*c.k,102254306099254+c.lower,102254687753054+c.upper)) = pointBounds23778 := by
 decide +kernel
def cuts23779 : List PrefixCut := [⟨95,403441667,403441897⟩,
⟨128,544683863,544684170⟩]
theorem checked23779 : checkPrefixCuts (2^48) 3120693249 9 Manual.Count131072.C023779.packed 128 cuts23779 = true := by
 decide +kernel
def pointBounds23779 : List (Nat × Nat × Nat) := [(3120790528,102255248835756,102255630490091)]
theorem point_links_checked23779 : (cuts23779.take 1).map (fun c => (3120693249-1+2*2^9*c.k,102254845394089+c.lower,102255227048194+c.upper)) = pointBounds23779 := by
 decide +kernel
def cuts23780 : List PrefixCut := [⟨63,269041387,269041542⟩,
⟨128,542496440,542496750⟩]
theorem checked23780 : checkPrefixCuts (2^48) 3120824321 9 Manual.Count131072.C023780.packed 128 cuts23780 = true := by
 decide +kernel
def pointBounds23780 : List (Nat × Nat × Nat) := [(3120888832,102255659119339,102256040773906)]
theorem point_links_checked23780 : (cuts23780.take 1).map (fun c => (3120824321-1+2*2^9*c.k,102255390077952+c.lower,102255771732364+c.upper)) = pointBounds23780 := by
 decide +kernel
def cuts23781 : List PrefixCut := [⟨31,132125776,132125847⟩,
⟨127,538505473,538505781⟩,
⟨128,543014719,543015030⟩]
theorem checked23781 : checkPrefixCuts (2^48) 3120955393 9 Manual.Count131072.C023781.packed 128 cuts23781 = true := by
 decide +kernel
def pointBounds23781 : List (Nat × Nat × Nat) := [(3120987136,102256064700168,102256446354961),(3121085440,102256471079865,102256852734895)]
theorem point_links_checked23781 : (cuts23781.take 2).map (fun c => (3120955393-1+2*2^9*c.k,102255932574392+c.lower,102256314229114+c.upper)) = pointBounds23781 := by
 decide +kernel
def cuts23782 : List PrefixCut := [⟨95,402488952,402489182⟩,
⟨128,540196279,540196584⟩]
theorem checked23782 : checkPrefixCuts (2^48) 3121086465 9 Manual.Count131072.C023782.packed 128 cuts23782 = true := by
 decide +kernel
def pointBounds23782 : List (Nat × Nat × Nat) := [(3121183744,102256878078063,102257259733326)]
theorem point_links_checked23782 : (cuts23782.take 1).map (fun c => (3121086465-1+2*2^9*c.k,102256475589111+c.lower,102256857244144+c.upper)) = pointBounds23782 := by
 decide +kernel
def cuts23783 : List PrefixCut := [⟨63,261973454,261973603⟩,
⟨128,536115470,536115772⟩]
theorem checked23783 : checkPrefixCuts (2^48) 3121217537 9 Manual.Count131072.C023783.packed 128 cuts23783 = true := by
 decide +kernel
def pointBounds23783 : List (Nat × Nat × Nat) := [(3121282048,102257277758844,102257659414331)]
theorem point_links_checked23783 : (cuts23783.take 1).map (fun c => (3121217537-1+2*2^9*c.k,102257015785390+c.lower,102257397440728+c.upper)) = pointBounds23783 := by
 decide +kernel
def cuts23784 : List PrefixCut := [⟨31,132650198,132650272⟩,
⟨127,541413503,541413810⟩,
⟨128,545110619,545110928⟩]
theorem checked23784 : checkPrefixCuts (2^48) 3121348609 9 Manual.Count131072.C023784.packed 128 cuts23784 = true := by
 decide +kernel
def pointBounds23784 : List (Nat × Nat × Nat) := [(3121380352,102257684551058,102258066206772),(3121478656,102258093314363,102258474970310)]
theorem point_links_checked23784 : (cuts23784.take 2).map (fun c => (3121348609-1+2*2^9*c.k,102257551900860+c.lower,102257933556500+c.upper)) = pointBounds23784 := by
 decide +kernel
def cuts23785 : List PrefixCut := [⟨95,404061386,404061617⟩,
⟨128,538505227,538505533⟩]
theorem checked23785 : checkPrefixCuts (2^48) 3121479681 9 Manual.Count131072.C023785.packed 128 cuts23785 = true := by
 decide +kernel
def pointBounds23785 : List (Nat × Nat × Nat) := [(3121576960,102258501072865,102258882729045)]
theorem point_links_checked23785 : (cuts23785.take 1).map (fun c => (3121479681-1+2*2^9*c.k,102258097011479+c.lower,102258478667428+c.upper)) = pointBounds23785 := by
 decide +kernel
def cuts23786 : List PrefixCut := [⟨63,266899696,266899854⟩,
⟨128,541097369,541097682⟩]
theorem checked23786 : checkPrefixCuts (2^48) 3121610753 9 Manual.Count131072.C023786.packed 128 cuts23786 = true := by
 decide +kernel
def pointBounds23786 : List (Nat × Nat × Nat) := [(3121675264,102258902416402,102259284072815)]
theorem point_links_checked23786 : (cuts23786.take 1).map (fun c => (3121610753-1+2*2^9*c.k,102258635516706+c.lower,102259017172961+c.upper)) = pointBounds23786 := by
 decide +kernel
def cuts23787 : List PrefixCut := [⟨31,133264642,133264716⟩,
⟨127,533410867,533411172⟩,
⟨128,537287842,537288149⟩]
theorem checked23787 : checkPrefixCuts (2^48) 3121741825 9 Manual.Count131072.C023787.packed 128 cuts23787 = true := by
 decide +kernel
def pointBounds23787 : List (Nat × Nat × Nat) := [(3121773568,102259309878717,102259691535359),(3121871872,102259710024942,102260091681815)]
theorem point_links_checked23787 : (cuts23787.take 2).map (fun c => (3121741825-1+2*2^9*c.k,102259176614075+c.lower,102259558270643+c.upper)) = pointBounds23787 := by
 decide +kernel
def cuts23788 : List PrefixCut := [⟨95,402657983,402658210⟩,
⟨128,543215704,543216016⟩]
theorem checked23788 : checkPrefixCuts (2^48) 3121872897 9 Manual.Count131072.C023788.packed 128 cuts23788 = true := by
 decide +kernel
def pointBounds23788 : List (Nat × Nat × Nat) := [(3121970176,102260116559900,102260498217002)]
theorem point_links_checked23788 : (cuts23788.take 1).map (fun c => (3121872897-1+2*2^9*c.k,102259713901917+c.lower,102260095558792+c.upper)) = pointBounds23788 := by
 decide +kernel
def cuts23789 : List PrefixCut := [⟨63,264341683,264341835⟩,
⟨128,537873717,537874028⟩]
theorem checked23789 : checkPrefixCuts (2^48) 3122003969 9 Manual.Count131072.C023789.packed 128 cuts23789 = true := by
 decide +kernel
def pointBounds23789 : List (Nat × Nat × Nat) := [(3122068480,102260521459304,102260903116643)]
theorem point_links_checked23789 : (cuts23789.take 1).map (fun c => (3122003969-1+2*2^9*c.k,102260257117621+c.lower,102260638774808+c.upper)) = pointBounds23789 := by
 decide +kernel
def cuts23790 : List PrefixCut := [⟨31,129100764,129100840⟩,
⟨127,535687576,535687882⟩,
⟨128,539744364,539744673⟩]
theorem checked23790 : checkPrefixCuts (2^48) 3122135041 9 Manual.Count131072.C023790.packed 128 cuts23790 = true := by
 decide +kernel
def pointBounds23790 : List (Nat × Nat × Nat) := [(3122166784,102260924092102,102261305749676),(3122265088,102261330678914,102261712336718)]
theorem point_links_checked23790 : (cuts23790.take 2).map (fun c => (3122135041-1+2*2^9*c.k,102260794991338+c.lower,102261176648836+c.upper)) = pointBounds23790 := by
 decide +kernel
def cuts23791 : List PrefixCut := [⟨95,404590624,404590856⟩,
⟨128,542426214,542426523⟩]
theorem checked23791 : checkPrefixCuts (2^48) 3122266113 9 Manual.Count131072.C023791.packed 128 cuts23791 = true := by
 decide +kernel
def pointBounds23791 : List (Nat × Nat × Nat) := [(3122363392,102261739326326,102262120984365)]
theorem point_links_checked23791 : (cuts23791.take 1).map (fun c => (3122266113-1+2*2^9*c.k,102261334735702+c.lower,102261716393509+c.upper)) = pointBounds23791 := by
 decide +kernel
def cuts23792 : List PrefixCut := [⟨63,265390181,265390326⟩,
⟨128,544026019,544026318⟩]
theorem checked23792 : checkPrefixCuts (2^48) 3122397185 9 Manual.Count131072.C023792.packed 128 cuts23792 = true := by
 decide +kernel
def pointBounds23792 : List (Nat × Nat × Nat) := [(3122461696,102262142552097,102262524210358)]
theorem point_links_checked23792 : (cuts23792.take 1).map (fun c => (3122397185-1+2*2^9*c.k,102261877161916+c.lower,102262258820032+c.upper)) = pointBounds23792 := by
 decide +kernel
def cuts23793 : List PrefixCut := [⟨31,132329635,132329710⟩,
⟨127,538414529,538414834⟩,
⟨128,542110248,542110556⟩]
theorem checked23793 : checkPrefixCuts (2^48) 3122528257 9 Manual.Count131072.C023793.packed 128 cuts23793 = true := by
 decide +kernel
def pointBounds23793 : List (Nat × Nat × Nat) := [(3122560000,102262553517570,102262935176060),(3122658304,102262959602464,102263341261184)]
theorem point_links_checked23793 : (cuts23793.take 2).map (fun c => (3122528257-1+2*2^9*c.k,102262421187935+c.lower,102262802846350+c.upper)) = pointBounds23793 := by
 decide +kernel
def cuts23794 : List PrefixCut := [⟨95,397689208,397689431⟩,
⟨128,537580564,537580869⟩]
theorem checked23794 : checkPrefixCuts (2^48) 3122659329 9 Manual.Count131072.C023794.packed 128 cuts23794 = true := by
 decide +kernel
def pointBounds23794 : List (Nat × Nat × Nat) := [(3122756608,102263360987391,102263742646337)]
theorem point_links_checked23794 : (cuts23794.take 1).map (fun c => (3122659329-1+2*2^9*c.k,102262963298183+c.lower,102263344956906+c.upper)) = pointBounds23794 := by
 decide +kernel
def cuts23795 : List PrefixCut := [⟨63,263013228,263013381⟩,
⟨128,537648084,537648389⟩]
theorem checked23795 : checkPrefixCuts (2^48) 3122790401 9 Manual.Count131072.C023795.packed 128 cuts23795 = true := by
 decide +kernel
def pointBounds23795 : List (Nat × Nat × Nat) := [(3122854912,102263763891975,102264145551156)]
theorem point_links_checked23795 : (cuts23795.take 1).map (fun c => (3122790401-1+2*2^9*c.k,102263500878747+c.lower,102263882537775+c.upper)) = pointBounds23795 := by
 decide +kernel
def cuts23796 : List PrefixCut := [⟨31,129879418,129879490⟩,
⟨127,540780231,540780536⟩,
⟨128,545016254,545016561⟩]
theorem checked23796 : checkPrefixCuts (2^48) 3122921473 9 Manual.Count131072.C023796.packed 128 cuts23796 = true := by
 decide +kernel
def pointBounds23796 : List (Nat × Nat × Nat) := [(3122953216,102264168406249,102264550065654),(3123051520,102264579307062,102264960966700)]
theorem point_links_checked23796 : (cuts23796.take 2).map (fun c => (3122921473-1+2*2^9*c.k,102264038526831+c.lower,102264420186164+c.upper)) = pointBounds23796 := by
 decide +kernel
def cuts23797 : List PrefixCut := [⟨95,397729267,397729490⟩,
⟨128,534628902,534629201⟩]
theorem checked23797 : checkPrefixCuts (2^48) 3123052545 9 Manual.Count131072.C023797.packed 128 cuts23797 = true := by
 decide +kernel
def pointBounds23797 : List (Nat × Nat × Nat) := [(3123149824,102264981272352,102265362932215)]
theorem point_links_checked23797 : (cuts23797.take 1).map (fun c => (3123052545-1+2*2^9*c.k,102264583543085+c.lower,102264965202725+c.upper)) = pointBounds23797 := by
 decide +kernel
def cuts23798 : List PrefixCut := [⟨63,266404851,266405000⟩,
⟨128,539473097,539473396⟩]
theorem checked23798 : checkPrefixCuts (2^48) 3123183617 9 Manual.Count131072.C023798.packed 128 cuts23798 = true := by
 decide +kernel
def pointBounds23798 : List (Nat × Nat × Nat) := [(3123248128,102265384576838,102265766236926)]
theorem point_links_checked23798 : (cuts23798.take 1).map (fun c => (3123183617-1+2*2^9*c.k,102265118171987+c.lower,102265499831926+c.upper)) = pointBounds23798 := by
 decide +kernel
def cuts23799 : List PrefixCut := [⟨31,133287645,133287718⟩,
⟨127,539540632,539540940⟩,
⟨128,543595888,543596198⟩]
theorem checked23799 : checkPrefixCuts (2^48) 3123314689 9 Manual.Count131072.C023799.packed 128 cuts23799 = true := by
 decide +kernel
def pointBounds23799 : List (Nat × Nat × Nat) := [(3123346432,102265790932729,102266172593040),(3123444736,102266197185716,102266578846262)]
theorem point_links_checked23799 : (cuts23799.take 2).map (fun c => (3123314689-1+2*2^9*c.k,102265657645084+c.lower,102266039305322+c.upper)) = pointBounds23799 := by
 decide +kernel
def cuts23800 : List PrefixCut := [⟨95,407321538,407321778⟩,
⟨128,549610745,549611062⟩]
theorem checked23800 : checkPrefixCuts (2^48) 3123445761 9 Manual.Count131072.C023800.packed 128 cuts23800 = true := by
 decide +kernel
def pointBounds23800 : List (Nat × Nat × Nat) := [(3123543040,102266608562510,102266990223298)]
theorem point_links_checked23800 : (cuts23800.take 1).map (fun c => (3123445761-1+2*2^9*c.k,102266201240972+c.lower,102266582901520+c.upper)) = pointBounds23800 := by
 decide +kernel
def cuts23801 : List PrefixCut := [⟨63,261324983,261325127⟩,
⟨128,543009447,543009742⟩]
theorem checked23801 : checkPrefixCuts (2^48) 3123576833 9 Manual.Count131072.C023801.packed 128 cuts23801 = true := by
 decide +kernel
def pointBounds23801 : List (Nat × Nat × Nat) := [(3123641344,102267012176700,102267393837709)]
theorem point_links_checked23801 : (cuts23801.take 1).map (fun c => (3123576833-1+2*2^9*c.k,102266750851717+c.lower,102267132512582+c.upper)) = pointBounds23801 := by
 decide +kernel
def cuts23802 : List PrefixCut := [⟨31,130657715,130657790⟩,
⟨127,532534476,532534786⟩,
⟨128,536318905,536319217⟩]
theorem checked23802 : checkPrefixCuts (2^48) 3123707905 9 Manual.Count131072.C023802.packed 128 cuts23802 = true := by
 decide +kernel
def pointBounds23802 : List (Nat × Nat × Nat) := [(3123739648,102267424518879,102267806180114),(3123837952,102267826395640,102268208057110)]
theorem point_links_checked23802 : (cuts23802.take 2).map (fun c => (3123707905-1+2*2^9*c.k,102267293861164+c.lower,102267675522324+c.upper)) = pointBounds23802 := by
 decide +kernel
def cuts23803 : List PrefixCut := [⟨95,402765071,402765294⟩,
⟨128,546658216,546658519⟩]
theorem checked23803 : checkPrefixCuts (2^48) 3123838977 9 Manual.Count131072.C023803.packed 128 cuts23803 = true := by
 decide +kernel
def pointBounds23803 : List (Nat × Nat × Nat) := [(3123936256,102268232945140,102268614606835)]
theorem point_links_checked23803 : (cuts23803.take 1).map (fun c => (3123838977-1+2*2^9*c.k,102267830180069+c.lower,102268211841541+c.upper)) = pointBounds23803 := by
 decide +kernel
def cuts23804 : List PrefixCut := [⟨63,267779397,267779545⟩,
⟨128,544743222,544743531⟩]
theorem checked23804 : checkPrefixCuts (2^48) 3123970049 9 Manual.Count131072.C023804.packed 128 cuts23804 = true := by
 decide +kernel
def pointBounds23804 : List (Nat × Nat × Nat) := [(3124034560,102268644617682,102269026279605)]
theorem point_links_checked23804 : (cuts23804.take 1).map (fun c => (3123970049-1+2*2^9*c.k,102268376838285+c.lower,102268758500060+c.upper)) = pointBounds23804 := by
 decide +kernel
def cuts23805 : List PrefixCut := [⟨31,130641261,130641334⟩,
⟨127,541116600,541116907⟩,
⟨128,545170835,545171145⟩]
theorem checked23805 : checkPrefixCuts (2^48) 3124101121 9 Manual.Count131072.C023805.packed 128 cuts23805 = true := by
 decide +kernel
def pointBounds23805 : List (Nat × Nat × Nat) := [(3124132864,102269052222768,102269433884925),(3124231168,102269462698107,102269844360498)]
theorem point_links_checked23805 : (cuts23805.take 2).map (fun c => (3124101121-1+2*2^9*c.k,102268921581507+c.lower,102269303243591+c.upper)) = pointBounds23805 := by
 decide +kernel
def cuts23806 : List PrefixCut := [⟨95,402624215,402624445⟩,
⟨128,540102795,540103105⟩]
theorem checked23806 : checkPrefixCuts (2^48) 3124232193 9 Manual.Count131072.C023806.packed 128 cuts23806 = true := by
 decide +kernel
def pointBounds23806 : List (Nat × Nat × Nat) := [(3124329472,102269869376557,102270251039181)]
theorem point_links_checked23806 : (cuts23806.take 1).map (fun c => (3124232193-1+2*2^9*c.k,102269466752342+c.lower,102269848414736+c.upper)) = pointBounds23806 := by
 decide +kernel
def cuts23807 : List PrefixCut := [⟨63,268556482,268556635⟩,
⟨128,537557765,537558071⟩]
theorem checked23807 : checkPrefixCuts (2^48) 3124363265 9 Manual.Count131072.C023807.packed 128 cuts23807 = true := by
 decide +kernel
def pointBounds23807 : List (Nat × Nat × Nat) := [(3124427776,102270275411619,102270657074476)]
theorem point_links_checked23807 : (cuts23807.take 1).map (fun c => (3124363265-1+2*2^9*c.k,102270006855137+c.lower,102270388517841+c.upper)) = pointBounds23807 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000118
