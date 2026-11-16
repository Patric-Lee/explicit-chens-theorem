import PlattAssemblyKernel
import PlattCertificates.Count131072.C023840
import PlattCertificates.Count131072.C023841
import PlattCertificates.Count131072.C023842
import PlattCertificates.Count131072.C023843
import PlattCertificates.Count131072.C023844
import PlattCertificates.Count131072.C023845
import PlattCertificates.Count131072.C023846
import PlattCertificates.Count131072.C023847
import PlattCertificates.Count131072.C023848
import PlattCertificates.Count131072.C023849
import PlattCertificates.Count131072.C023850
import PlattCertificates.Count131072.C023851
import PlattCertificates.Count131072.C023852
import PlattCertificates.Count131072.C023853
import PlattCertificates.Count131072.C023854
import PlattCertificates.Count131072.C023855
import PlattCertificates.Count131072.C023856
import PlattCertificates.Count131072.C023857
import PlattCertificates.Count131072.C023858
import PlattCertificates.Count131072.C023859
import PlattCertificates.Count131072.C023860
import PlattCertificates.Count131072.C023861
import PlattCertificates.Count131072.C023862
import PlattCertificates.Count131072.C023863
import PlattCertificates.Count131072.C023864
import PlattCertificates.Count131072.C023865
import PlattCertificates.Count131072.C023866
import PlattCertificates.Count131072.C023867
import PlattCertificates.Count131072.C023868
import PlattCertificates.Count131072.C023869
import PlattCertificates.Count131072.C023870
import PlattCertificates.Count131072.C023871
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000120
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23840 : List PrefixCut := [⟨63,266835732,266835884⟩,
⟨128,543651794,543652105⟩]
theorem checked23840 : checkPrefixCuts (2^48) 3128688641 9 Manual.Count131072.C023840.packed 128 cuts23840 = true := by
 decide +kernel
def pointBounds23840 : List (Nat × Nat × Nat) := [(3128753152,102288067380193,102288449053118)]
theorem point_links_checked23840 : (cuts23840.take 1).map (fun c => (3128688641-1+2*2^9*c.k,102287800544461+c.lower,102288182217234+c.upper)) = pointBounds23840 := by
 decide +kernel
def cuts23841 : List PrefixCut := [⟨31,131163947,131164020⟩,
⟨127,539580934,539581237⟩,
⟨128,543089306,543089611⟩]
theorem checked23841 : checkPrefixCuts (2^48) 3128819713 9 Manual.Count131072.C023841.packed 128 cuts23841 = true := by
 decide +kernel
def pointBounds23841 : List (Nat × Nat × Nat) := [(3128851456,102288475360202,102288857033359),(3128949760,102288883777189,102289265450576)]
theorem point_links_checked23841 : (cuts23841.take 2).map (fun c => (3128819713-1+2*2^9*c.k,102288344196255+c.lower,102288725869339+c.upper)) = pointBounds23841 := by
 decide +kernel
def cuts23842 : List PrefixCut := [⟨95,401027626,401027852⟩,
⟨128,543246401,543246705⟩]
theorem checked23842 : checkPrefixCuts (2^48) 3128950785 9 Manual.Count131072.C023842.packed 128 cuts23842 = true := by
 decide +kernel
def pointBounds23842 : List (Nat × Nat × Nat) := [(3129048064,102289288313187,102289669986802)]
theorem point_links_checked23842 : (cuts23842.take 1).map (fun c => (3128950785-1+2*2^9*c.k,102288887285561+c.lower,102289268958950+c.upper)) = pointBounds23842 := by
 decide +kernel
def cuts23843 : List PrefixCut := [⟨63,264913205,264913355⟩,
⟨128,541064799,541065104⟩]
theorem checked23843 : checkPrefixCuts (2^48) 3129081857 9 Manual.Count131072.C023843.packed 128 cuts23843 = true := by
 decide +kernel
def pointBounds23843 : List (Nat × Nat × Nat) := [(3129146368,102289695445167,102290077119010)]
theorem point_links_checked23843 : (cuts23843.take 1).map (fun c => (3129081857-1+2*2^9*c.k,102289430531962+c.lower,102289812205655+c.upper)) = pointBounds23843 := by
 decide +kernel
def cuts23844 : List PrefixCut := [⟨31,130247954,130248030⟩,
⟨127,535465353,535465653⟩,
⟨128,538883337,538883639⟩]
theorem checked23844 : checkPrefixCuts (2^48) 3129212929 9 Manual.Count131072.C023844.packed 128 cuts23844 = true := by
 decide +kernel
def pointBounds23844 : List (Nat × Nat × Nat) := [(3129244672,102290101844715,102290483518789),(3129342976,102290507062114,102290888736412)]
theorem point_links_checked23844 : (cuts23844.take 2).map (fun c => (3129212929-1+2*2^9*c.k,102289971596761+c.lower,102290353270759+c.upper)) = pointBounds23844 := by
 decide +kernel
def cuts23845 : List PrefixCut := [⟨95,403046011,403046238⟩,
⟨128,540479910,540480219⟩]
theorem checked23845 : checkPrefixCuts (2^48) 3129344001 9 Manual.Count131072.C023845.packed 128 cuts23845 = true := by
 decide +kernel
def pointBounds23845 : List (Nat × Nat × Nat) := [(3129441280,102290913526109,102291295200636)]
theorem point_links_checked23845 : (cuts23845.take 1).map (fun c => (3129344001-1+2*2^9*c.k,102290510480098+c.lower,102290892154398+c.upper)) = pointBounds23845 := by
 decide +kernel
def cuts23846 : List PrefixCut := [⟨63,264700030,264700177⟩,
⟨128,538388558,538388858⟩]
theorem checked23846 : checkPrefixCuts (2^48) 3129475073 9 Manual.Count131072.C023846.packed 128 cuts23846 = true := by
 decide +kernel
def pointBounds23846 : List (Nat × Nat × Nat) := [(3129539584,102291315660038,102291697334794)]
theorem point_links_checked23846 : (cuts23846.take 1).map (fun c => (3129475073-1+2*2^9*c.k,102291050960008+c.lower,102291432634617+c.upper)) = pointBounds23846 := by
 decide +kernel
def cuts23847 : List PrefixCut := [⟨31,132749873,132749955⟩,
⟨127,542323322,542323635⟩,
⟨128,546550297,546550613⟩]
theorem checked23847 : checkPrefixCuts (2^48) 3129606145 9 Manual.Count131072.C023847.packed 128 cuts23847 = true := by
 decide +kernel
def pointBounds23847 : List (Nat × Nat × Nat) := [(3129637888,102291722098439,102292103773430),(3129736192,102292131671888,102292513347110)]
theorem point_links_checked23847 : (cuts23847.take 2).map (fun c => (3129606145-1+2*2^9*c.k,102291589348566+c.lower,102291971023475+c.upper)) = pointBounds23847 := by
 decide +kernel
def cuts23848 : List PrefixCut := [⟨95,401106653,401106872⟩,
⟨128,539152810,539153109⟩]
theorem checked23848 : checkPrefixCuts (2^48) 3129737217 9 Manual.Count131072.C023848.packed 128 cuts23848 = true := by
 decide +kernel
def pointBounds23848 : List (Nat × Nat × Nat) := [(3129834496,102292537005516,102292918680960)]
theorem point_links_checked23848 : (cuts23848.take 1).map (fun c => (3129737217-1+2*2^9*c.k,102292135898863+c.lower,102292517574088+c.upper)) = pointBounds23848 := by
 decide +kernel
def cuts23849 : List PrefixCut := [⟨63,267634466,267634614⟩,
⟨128,540479281,540479577⟩]
theorem checked23849 : checkPrefixCuts (2^48) 3129868289 9 Manual.Count131072.C023849.packed 128 cuts23849 = true := by
 decide +kernel
def pointBounds23849 : List (Nat × Nat × Nat) := [(3129932800,102292942686139,102293324361811)]
theorem point_links_checked23849 : (cuts23849.take 1).map (fun c => (3129868289-1+2*2^9*c.k,102292675051673+c.lower,102293056727197+c.upper)) = pointBounds23849 := by
 decide +kernel
def cuts23850 : List PrefixCut := [⟨31,130215227,130215296⟩,
⟨127,529305849,529306150⟩,
⟨128,533262520,533262824⟩]
theorem checked23850 : checkPrefixCuts (2^48) 3129999361 9 Manual.Count131072.C023850.packed 128 cuts23850 = true := by
 decide +kernel
def pointBounds23850 : List (Nat × Nat × Nat) := [(3130031104,102293345746181,102293727422070),(3130129408,102293744836803,102294126512924)]
theorem point_links_checked23850 : (cuts23850.take 2).map (fun c => (3129999361-1+2*2^9*c.k,102293215530954+c.lower,102293597206774+c.upper)) = pointBounds23850 := by
 decide +kernel
def cuts23851 : List PrefixCut := [⟨95,399437714,399437937⟩,
⟨128,540703701,540704002⟩]
theorem checked23851 : checkPrefixCuts (2^48) 3130130433 9 Manual.Count131072.C023851.packed 128 cuts23851 = true := by
 decide +kernel
def pointBounds23851 : List (Nat × Nat × Nat) := [(3130227712,102294148231188,102294529907535)]
theorem point_links_checked23851 : (cuts23851.take 1).map (fun c => (3130130433-1+2*2^9*c.k,102293748793474+c.lower,102294130469598+c.upper)) = pointBounds23851 := by
 decide +kernel
def cuts23852 : List PrefixCut := [⟨63,266162149,266162292⟩,
⟨128,544457639,544457935⟩]
theorem checked23852 : checkPrefixCuts (2^48) 3130261505 9 Manual.Count131072.C023852.packed 128 cuts23852 = true := by
 decide +kernel
def pointBounds23852 : List (Nat × Nat × Nat) := [(3130326016,102294555659324,102294937335892)]
theorem point_links_checked23852 : (cuts23852.take 1).map (fun c => (3130261505-1+2*2^9*c.k,102294289497175+c.lower,102294671173600+c.upper)) = pointBounds23852 := by
 decide +kernel
def cuts23853 : List PrefixCut := [⟨31,131277860,131277935⟩,
⟨127,533015712,533016014⟩,
⟨128,536881973,536882278⟩]
theorem checked23853 : checkPrefixCuts (2^48) 3130392577 9 Manual.Count131072.C023853.packed 128 cuts23853 = true := by
 decide +kernel
def pointBounds23853 : List (Nat × Nat × Nat) := [(3130424320,102294965232674,102295346909470),(3130522624,102295366970526,102295748647549)]
theorem point_links_checked23853 : (cuts23853.take 2).map (fun c => (3130392577-1+2*2^9*c.k,102294833954814+c.lower,102295215631535+c.upper)) = pointBounds23853 := by
 decide +kernel
def cuts23854 : List PrefixCut := [⟨95,398218651,398218875⟩,
⟨128,537758591,537758892⟩]
theorem checked23854 : checkPrefixCuts (2^48) 3130523649 9 Manual.Count131072.C023854.packed 128 cuts23854 = true := by
 decide +kernel
def pointBounds23854 : List (Nat × Nat × Nat) := [(3130620928,102295769055438,102296150732688)]
theorem point_links_checked23854 : (cuts23854.take 1).map (fun c => (3130523649-1+2*2^9*c.k,102295370836787+c.lower,102295752513813+c.upper)) = pointBounds23854 := by
 decide +kernel
def cuts23855 : List PrefixCut := [⟨63,269545213,269545361⟩,
⟨128,541961837,541962137⟩]
theorem checked23855 : checkPrefixCuts (2^48) 3130654721 9 Manual.Count131072.C023855.packed 128 cuts23855 = true := by
 decide +kernel
def pointBounds23855 : List (Nat × Nat × Nat) := [(3130719232,102296178140591,102296559818066)]
theorem point_links_checked23855 : (cuts23855.take 1).map (fun c => (3130654721-1+2*2^9*c.k,102295908595378+c.lower,102296290272705+c.upper)) = pointBounds23855 := by
 decide +kernel
def cuts23856 : List PrefixCut := [⟨31,131261375,131261446⟩,
⟨127,538792500,538792805⟩,
⟨128,543107785,543108092⟩]
theorem checked23856 : checkPrefixCuts (2^48) 3130785793 9 Manual.Count131072.C023856.packed 128 cuts23856 = true := by
 decide +kernel
def pointBounds23856 : List (Nat × Nat × Nat) := [(3130817536,102296581818590,102296963496288),(3130915840,102296989349715,102297371027647)]
theorem point_links_checked23856 : (cuts23856.take 2).map (fun c => (3130785793-1+2*2^9*c.k,102296450557215+c.lower,102296832234842+c.upper)) = pointBounds23856 := by
 decide +kernel
def cuts23857 : List PrefixCut := [⟨95,401674815,401675038⟩,
⟨128,545422469,545422767⟩]
theorem checked23857 : checkPrefixCuts (2^48) 3130916865 9 Manual.Count131072.C023857.packed 128 cuts23857 = true := by
 decide +kernel
def pointBounds23857 : List (Nat × Nat × Nat) := [(3131014144,102297395339815,102297777017972)]
theorem point_links_checked23857 : (cuts23857.take 1).map (fun c => (3130916865-1+2*2^9*c.k,102296993665000+c.lower,102297375342934+c.upper)) = pointBounds23857 := by
 decide +kernel
def cuts23858 : List PrefixCut := [⟨63,263937787,263937936⟩,
⟨128,537758490,537758798⟩]
theorem checked23858 : checkPrefixCuts (2^48) 3131047937 9 Manual.Count131072.C023858.packed 128 cuts23858 = true := by
 decide +kernel
def pointBounds23858 : List (Nat × Nat × Nat) := [(3131112448,102297803025256,102298184703637)]
theorem point_links_checked23858 : (cuts23858.take 1).map (fun c => (3131047937-1+2*2^9*c.k,102297539087469+c.lower,102297920765701+c.upper)) = pointBounds23858 := by
 decide +kernel
def cuts23859 : List PrefixCut := [⟨31,130076275,130076348⟩,
⟨127,534230226,534230527⟩,
⟨128,538095516,538095820⟩]
theorem checked23859 : checkPrefixCuts (2^48) 3131179009 9 Manual.Count131072.C023859.packed 128 cuts23859 = true := by
 decide +kernel
def pointBounds23859 : List (Nat × Nat × Nat) := [(3131210752,102298206922234,102298588600847),(3131309056,102298611076185,102298992755026)]
theorem point_links_checked23859 : (cuts23859.take 2).map (fun c => (3131179009-1+2*2^9*c.k,102298076845959+c.lower,102298458524499+c.upper)) = pointBounds23859 := by
 decide +kernel
def cuts23860 : List PrefixCut := [⟨95,397219785,397220015⟩,
⟨128,537264005,537264318⟩]
theorem checked23860 : checkPrefixCuts (2^48) 3131310081 9 Manual.Count131072.C023860.packed 128 cuts23860 = true := by
 decide +kernel
def pointBounds23860 : List (Nat × Nat × Nat) := [(3131407360,102299012161260,102299393840334)]
theorem point_links_checked23860 : (cuts23860.take 1).map (fun c => (3131310081-1+2*2^9*c.k,102298614941475+c.lower,102298996620319+c.upper)) = pointBounds23860 := by
 decide +kernel
def cuts23861 : List PrefixCut := [⟨63,262825940,262826090⟩,
⟨128,534365155,534365458⟩]
theorem checked23861 : checkPrefixCuts (2^48) 3131441153 9 Manual.Count131072.C023861.packed 128 cuts23861 = true := by
 decide +kernel
def pointBounds23861 : List (Nat × Nat × Nat) := [(3131505664,102299415031420,102299796710727)]
theorem point_links_checked23861 : (cuts23861.take 1).map (fun c => (3131441153-1+2*2^9*c.k,102299152205480+c.lower,102299533884637+c.upper)) = pointBounds23861 := by
 decide +kernel
def cuts23862 : List PrefixCut := [⟨31,127003944,127004019⟩,
⟨127,530028592,530028891⟩,
⟨128,533533880,533534181⟩]
theorem checked23862 : checkPrefixCuts (2^48) 3131572225 9 Manual.Count131072.C023862.packed 128 cuts23862 = true := by
 decide +kernel
def pointBounds23862 : List (Nat × Nat × Nat) := [(3131603968,102299813574579,102300195254114),(3131702272,102300216599227,102300598278986)]
theorem point_links_checked23862 : (cuts23862.take 2).map (fun c => (3131572225-1+2*2^9*c.k,102299686570635+c.lower,102300068250095+c.upper)) = pointBounds23862 := by
 decide +kernel
def cuts23863 : List PrefixCut := [⟨95,397709135,397709360⟩,
⟨128,536657267,536657571⟩]
theorem checked23863 : checkPrefixCuts (2^48) 3131703297 9 Manual.Count131072.C023863.packed 128 cuts23863 = true := by
 decide +kernel
def pointBounds23863 : List (Nat × Nat × Nat) := [(3131800576,102300617813650,102300999493636)]
theorem point_links_checked23863 : (cuts23863.take 1).map (fun c => (3131703297-1+2*2^9*c.k,102300220104515+c.lower,102300601784276+c.upper)) = pointBounds23863 := by
 decide +kernel
def cuts23864 : List PrefixCut := [⟨63,259377746,259377890⟩,
⟨128,534208182,534208483⟩]
theorem checked23864 : checkPrefixCuts (2^48) 3131834369 9 Manual.Count131072.C023864.packed 128 cuts23864 = true := by
 decide +kernel
def pointBounds23864 : List (Nat × Nat × Nat) := [(3131898880,102301016139528,102301397819737)]
theorem point_links_checked23864 : (cuts23864.take 1).map (fun c => (3131834369-1+2*2^9*c.k,102300756761782+c.lower,102301138441847+c.upper)) = pointBounds23864 := by
 decide +kernel
def cuts23865 : List PrefixCut := [⟨31,127527221,127527292⟩,
⟨127,529243127,529243424⟩,
⟨128,532927711,532928010⟩]
theorem checked23865 : checkPrefixCuts (2^48) 3131965441 9 Manual.Count131072.C023865.packed 128 cuts23865 = true := by
 decide +kernel
def pointBounds23865 : List (Nat × Nat × Nat) := [(3131997184,102301418497185,102301800177622),(3132095488,102301820213091,102302201893754)]
theorem point_links_checked23865 : (cuts23865.take 2).map (fun c => (3131965441-1+2*2^9*c.k,102301290969964+c.lower,102301672650330+c.upper)) = pointBounds23865 := by
 decide +kernel
def cuts23866 : List PrefixCut := [⟨95,393794945,393795169⟩,
⟨128,531647265,531647565⟩]
theorem checked23866 : checkPrefixCuts (2^48) 3132096513 9 Manual.Count131072.C023866.packed 128 cuts23866 = true := by
 decide +kernel
def pointBounds23866 : List (Nat × Nat × Nat) := [(3132193792,102302217692620,102302599373509)]
theorem point_links_checked23866 : (cuts23866.take 1).map (fun c => (3132096513-1+2*2^9*c.k,102301823897675+c.lower,102302205578340+c.upper)) = pointBounds23866 := by
 decide +kernel
def cuts23867 : List PrefixCut := [⟨63,267343046,267343203⟩,
⟨128,537645914,537646223⟩]
theorem checked23867 : checkPrefixCuts (2^48) 3132227585 9 Manual.Count131072.C023867.packed 128 cuts23867 = true := by
 decide +kernel
def pointBounds23867 : List (Nat × Nat × Nat) := [(3132292096,102302622887986,102303004569108)]
theorem point_links_checked23867 : (cuts23867.take 1).map (fun c => (3132227585-1+2*2^9*c.k,102302355544940+c.lower,102302737225905+c.upper)) = pointBounds23867 := by
 decide +kernel
def cuts23868 : List PrefixCut := [⟨31,129488135,129488208⟩,
⟨127,536185630,536185930⟩,
⟨128,539779895,539780197⟩]
theorem checked23868 : checkPrefixCuts (2^48) 3132358657 9 Manual.Count131072.C023868.packed 128 cuts23868 = true := by
 decide +kernel
def pointBounds23868 : List (Nat × Nat × Nat) := [(3132390400,102303022678989,102303404360336),(3132488704,102303429376484,102303811058058)]
theorem point_links_checked23868 : (cuts23868.take 2).map (fun c => (3132358657-1+2*2^9*c.k,102302893190854+c.lower,102303274872128+c.upper)) = pointBounds23868 := by
 decide +kernel
def cuts23869 : List PrefixCut := [⟨95,404258539,404258769⟩,
⟨128,538768971,538769280⟩]
theorem checked23869 : checkPrefixCuts (2^48) 3132489729 9 Manual.Count131072.C023869.packed 128 cuts23869 = true := by
 decide +kernel
def pointBounds23869 : List (Nat × Nat × Nat) := [(3132587008,102303837229288,102304218911094)]
theorem point_links_checked23869 : (cuts23869.take 1).map (fun c => (3132489729-1+2*2^9*c.k,102303432970749+c.lower,102303814652325+c.upper)) = pointBounds23869 := by
 decide +kernel
def cuts23870 : List PrefixCut := [⟨63,264793621,264793774⟩,
⟨128,532726439,532726746⟩]
theorem checked23870 : checkPrefixCuts (2^48) 3132620801 9 Manual.Count131072.C023870.packed 128 cuts23870 = true := by
 decide +kernel
def pointBounds23870 : List (Nat × Nat × Nat) := [(3132685312,102304236533341,102304618215379)]
theorem point_links_checked23870 : (cuts23870.take 1).map (fun c => (3132620801-1+2*2^9*c.k,102303971739720+c.lower,102304353421605+c.upper)) = pointBounds23870 := by
 decide +kernel
def cuts23871 : List PrefixCut := [⟨31,129831285,129831356⟩,
⟨127,532344820,532345116⟩,
⟨128,537196469,537196767⟩]
theorem checked23871 : checkPrefixCuts (2^48) 3132751873 9 Manual.Count131072.C023871.packed 128 cuts23871 = true := by
 decide +kernel
def pointBounds23871 : List (Nat × Nat × Nat) := [(3132783616,102304634297444,102305015979707),(3132881920,102305036810979,102305418493467)]
theorem point_links_checked23871 : (cuts23871.take 2).map (fun c => (3132751873-1+2*2^9*c.k,102304504466159+c.lower,102304886148351+c.upper)) = pointBounds23871 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000120
