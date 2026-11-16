import PlattAssemblyKernel
import PlattCertificates.Count131072.C022848
import PlattCertificates.Count131072.C022849
import PlattCertificates.Count131072.C022850
import PlattCertificates.Count131072.C022851
import PlattCertificates.Count131072.C022852
import PlattCertificates.Count131072.C022853
import PlattCertificates.Count131072.C022854
import PlattCertificates.Count131072.C022855
import PlattCertificates.Count131072.C022856
import PlattCertificates.Count131072.C022857
import PlattCertificates.Count131072.C022858
import PlattCertificates.Count131072.C022859
import PlattCertificates.Count131072.C022860
import PlattCertificates.Count131072.C022861
import PlattCertificates.Count131072.C022862
import PlattCertificates.Count131072.C022863
import PlattCertificates.Count131072.C022864
import PlattCertificates.Count131072.C022865
import PlattCertificates.Count131072.C022866
import PlattCertificates.Count131072.C022867
import PlattCertificates.Count131072.C022868
import PlattCertificates.Count131072.C022869
import PlattCertificates.Count131072.C022870
import PlattCertificates.Count131072.C022871
import PlattCertificates.Count131072.C022872
import PlattCertificates.Count131072.C022873
import PlattCertificates.Count131072.C022874
import PlattCertificates.Count131072.C022875
import PlattCertificates.Count131072.C022876
import PlattCertificates.Count131072.C022877
import PlattCertificates.Count131072.C022878
import PlattCertificates.Count131072.C022879
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000089
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22848 : List PrefixCut := [⟨72,320457028,320457207⟩,
⟨128,560841508,560841827⟩]
theorem checked22848 : checkPrefixCuts (2^48) 2998665217 9 Manual.Count131072.C022848.packed 128 cuts22848 = true := by
 decide +kernel
def pointBounds22848 : List (Nat × Nat × Nat) := [(2998738944,101741171771809,101741553134732)]
theorem point_links_checked22848 : (cuts22848.take 1).map (fun c => (2998665217-1+2*2^9*c.k,101740851314781+c.lower,101741232677525+c.upper)) = pointBounds22848 := by
 decide +kernel
def cuts22849 : List PrefixCut := [⟨36,159659356,159659444⟩,
⟨128,561849447,561849763⟩]
theorem checked22849 : checkPrefixCuts (2^48) 2998796289 9 Manual.Count131072.C022849.packed 128 cuts22849 = true := by
 decide +kernel
def pointBounds22849 : List (Nat × Nat × Nat) := [(2998833152,101741571815645,101741953178796),(2998927360,101741974005736,101742355369115)]
theorem point_links_checked22849 : (cuts22849.take 2).map (fun c => (2998796289-1+2*2^9*c.k,101741412156289+c.lower,101741793519352+c.upper)) = pointBounds22849 := by
 decide +kernel
def cuts22850 : List PrefixCut := [⟨92,403209838,403210078⟩,
⟨128,558727555,558727888⟩]
theorem checked22850 : checkPrefixCuts (2^48) 2998927361 9 Manual.Count131072.C022850.packed 128 cuts22850 = true := by
 decide +kernel
def pointBounds22850 : List (Nat × Nat × Nat) := [(2999021568,101742377215574,101742758579193)]
theorem point_links_checked22850 : (cuts22850.take 1).map (fun c => (2998927361-1+2*2^9*c.k,101741974005736+c.lower,101742355369115+c.upper)) = pointBounds22850 := by
 decide +kernel
def cuts22851 : List PrefixCut := [⟨56,245145398,245145539⟩,
⟨128,561143313,561143635⟩]
theorem checked22851 : checkPrefixCuts (2^48) 2999058433 9 Manual.Count131072.C022851.packed 128 cuts22851 = true := by
 decide +kernel
def pointBounds22851 : List (Nat × Nat × Nat) := [(2999115776,101742777878689,101743159242542)]
theorem point_links_checked22851 : (cuts22851.take 1).map (fun c => (2999058433-1+2*2^9*c.k,101742532733291+c.lower,101742914097003+c.upper)) = pointBounds22851 := by
 decide +kernel
def cuts22852 : List PrefixCut := [⟨20,90095993,90096045⟩,
⟨112,491954018,491954304⟩,
⟨128,562338879,562339204⟩]
theorem checked22852 : checkPrefixCuts (2^48) 2999189505 9 Manual.Count131072.C022852.packed 128 cuts22852 = true := by
 decide +kernel
def pointBounds22852 : List (Nat × Nat × Nat) := [(2999209984,101743183972597,101743565336683),(2999304192,101743585830622,101743967194942)]
theorem point_links_checked22852 : (cuts22852.take 2).map (fun c => (2999189505-1+2*2^9*c.k,101743093876604+c.lower,101743475240638+c.upper)) = pointBounds22852 := by
 decide +kernel
def cuts22853 : List PrefixCut := [⟨76,330428181,330428368⟩,
⟨128,556402018,556402330⟩]
theorem checked22853 : checkPrefixCuts (2^48) 2999320577 9 Manual.Count131072.C022853.packed 128 cuts22853 = true := by
 decide +kernel
def pointBounds22853 : List (Nat × Nat × Nat) := [(2999398400,101743986643664,101744368008210)]
theorem point_links_checked22853 : (cuts22853.take 1).map (fun c => (2999320577-1+2*2^9*c.k,101743656215483+c.lower,101744037579842+c.upper)) = pointBounds22853 := by
 decide +kernel
def cuts22854 : List PrefixCut := [⟨40,180457162,180457262⟩,
⟨128,567544834,567545152⟩]
theorem checked22854 : checkPrefixCuts (2^48) 2999451649 9 Manual.Count131072.C022854.packed 128 cuts22854 = true := by
 decide +kernel
def pointBounds22854 : List (Nat × Nat × Nat) := [(2999492608,101744393074663,101744774439434)]
theorem point_links_checked22854 : (cuts22854.take 1).map (fun c => (2999451649-1+2*2^9*c.k,101744212617501+c.lower,101744593982172+c.upper)) = pointBounds22854 := by
 decide +kernel
def cuts22855 : List PrefixCut := [⟨4,17266183,17266193⟩,
⟨96,420575195,420575436⟩,
⟨128,562922022,562922343⟩]
theorem checked22855 : checkPrefixCuts (2^48) 2999582721 9 Manual.Count131072.C022855.packed 128 cuts22855 = true := by
 decide +kernel
def pointBounds22855 : List (Nat × Nat × Nat) := [(2999586816,101744797428518,101745178793517),(2999681024,101745200737530,101745582102760)]
theorem point_links_checked22855 : (cuts22855.take 2).map (fun c => (2999582721-1+2*2^9*c.k,101744780162335+c.lower,101745161527324+c.upper)) = pointBounds22855 := by
 decide +kernel
def cuts22856 : List PrefixCut := [⟨60,261981601,261981745⟩,
⟨128,562146652,562146969⟩]
theorem checked22856 : checkPrefixCuts (2^48) 2999713793 9 Manual.Count131072.C022856.packed 128 cuts22856 = true := by
 decide +kernel
def pointBounds22856 : List (Nat × Nat × Nat) := [(2999775232,101745605065958,101745986431412)]
theorem point_links_checked22856 : (cuts22856.take 1).map (fun c => (2999713793-1+2*2^9*c.k,101745343084357+c.lower,101745724449667+c.upper)) = pointBounds22856 := by
 decide +kernel
def cuts22857 : List PrefixCut := [⟨24,101992588,101992644⟩,
⟨116,510142562,510142848⟩,
⟨128,561934465,561934783⟩]
theorem checked22857 : checkPrefixCuts (2^48) 2999844865 9 Manual.Count131072.C022857.packed 128 cuts22857 = true := by
 decide +kernel
def pointBounds22857 : List (Nat × Nat × Nat) := [(2999869440,101746007223597,101746388589280),(2999963648,101746415373571,101746796739484)]
theorem point_links_checked22857 : (cuts22857.take 2).map (fun c => (2999844865-1+2*2^9*c.k,101745905231009+c.lower,101746286596636+c.upper)) = pointBounds22857 := by
 decide +kernel
def cuts22858 : List PrefixCut := [⟨80,359722936,359723143⟩,
⟨128,571667702,571668028⟩]
theorem checked22858 : checkPrefixCuts (2^48) 2999975937 9 Manual.Count131072.C022858.packed 128 cuts22858 = true := by
 decide +kernel
def pointBounds22858 : List (Nat × Nat × Nat) := [(3000057856,101746826888410,101747208254562)]
theorem point_links_checked22858 : (cuts22858.take 1).map (fun c => (2999975937-1+2*2^9*c.k,101746467165474+c.lower,101746848531419+c.upper)) = pointBounds22858 := by
 decide +kernel
def cuts22859 : List PrefixCut := [⟨44,190174979,190175093⟩,
⟨128,563574053,563574375⟩]
theorem checked22859 : checkPrefixCuts (2^48) 3000107009 9 Manual.Count131072.C022859.packed 128 cuts22859 = true := by
 decide +kernel
def pointBounds22859 : List (Nat × Nat × Nat) := [(3000152064,101747229008155,101747610374540)]
theorem point_links_checked22859 : (cuts22859.take 1).map (fun c => (3000107009-1+2*2^9*c.k,101747038833176+c.lower,101747420199447+c.upper)) = pointBounds22859 := by
 decide +kernel
def cuts22860 : List PrefixCut := [⟨8,34618618,34618637⟩,
⟨100,439058551,439058806⟩,
⟨128,566551600,566551925⟩]
theorem checked22860 : checkPrefixCuts (2^48) 3000238081 9 Manual.Count131072.C022860.packed 128 cuts22860 = true := by
 decide +kernel
def pointBounds22860 : List (Nat × Nat × Nat) := [(3000246272,101747637025847,101748018392459),(3000340480,101748041465780,101748422832628)]
theorem point_links_checked22860 : (cuts22860.take 2).map (fun c => (3000238081-1+2*2^9*c.k,101747602407229+c.lower,101747983773822+c.upper)) = pointBounds22860 := by
 decide +kernel
def cuts22861 : List PrefixCut := [⟨64,281437219,281437382⟩,
⟨128,565776363,565776692⟩]
theorem checked22861 : checkPrefixCuts (2^48) 3000369153 9 Manual.Count131072.C022861.packed 128 cuts22861 = true := by
 decide +kernel
def pointBounds22861 : List (Nat × Nat × Nat) := [(3000434688,101748450396048,101748831763129)]
theorem point_links_checked22861 : (cuts22861.take 1).map (fun c => (3000369153-1+2*2^9*c.k,101748168958829+c.lower,101748550325747+c.upper)) = pointBounds22861 := by
 decide +kernel
def cuts22862 : List PrefixCut := [⟨28,122983428,122983499⟩,
⟨120,526728575,526728876⟩,
⟨128,561999385,561999707⟩]
theorem checked22862 : checkPrefixCuts (2^48) 3000500225 9 Manual.Count131072.C022862.packed 128 cuts22862 = true := by
 decide +kernel
def pointBounds22862 : List (Nat × Nat × Nat) := [(3000528896,101748857718620,101749239085938),(3000623104,101749261463767,101749642831315)]
theorem point_links_checked22862 : (cuts22862.take 2).map (fun c => (3000500225-1+2*2^9*c.k,101748734735192+c.lower,101749116102439+c.upper)) = pointBounds22862 := by
 decide +kernel
def cuts22863 : List PrefixCut := [⟨84,367429756,367429969⟩,
⟨128,564882603,564882924⟩]
theorem checked22863 : checkPrefixCuts (2^48) 3000631297 9 Manual.Count131072.C022863.packed 128 cuts22863 = true := by
 decide +kernel
def pointBounds22863 : List (Nat × Nat × Nat) := [(3000717312,101749664164333,101750045532115)]
theorem point_links_checked22863 : (cuts22863.take 1).map (fun c => (3000631297-1+2*2^9*c.k,101749296734577+c.lower,101749678102146+c.upper)) = pointBounds22863 := by
 decide +kernel
def cuts22864 : List PrefixCut := [⟨48,205797961,205798082⟩,
⟨128,553695931,553696245⟩]
theorem checked22864 : checkPrefixCuts (2^48) 3000762369 9 Manual.Count131072.C022864.packed 128 cuts22864 = true := by
 decide +kernel
def pointBounds22864 : List (Nat × Nat × Nat) := [(3000811520,101750067415141,101750448783152)]
theorem point_links_checked22864 : (cuts22864.take 1).map (fun c => (3000762369-1+2*2^9*c.k,101749861617180+c.lower,101750242985070+c.upper)) = pointBounds22864 := by
 decide +kernel
def cuts22865 : List PrefixCut := [⟨12,54120779,54120808⟩,
⟨104,463536733,463536992⟩,
⟨128,571117663,571117979⟩]
theorem checked22865 : checkPrefixCuts (2^48) 3000893441 9 Manual.Count131072.C022865.packed 128 cuts22865 = true := by
 decide +kernel
def pointBounds22865 : List (Nat × Nat × Nat) := [(3000905728,101750469433890,101750850802123),(3000999936,101750878849844,101751260218307)]
theorem point_links_checked22865 : (cuts22865.take 2).map (fun c => (3000893441-1+2*2^9*c.k,101750415313111+c.lower,101750796681315+c.upper)) = pointBounds22865 := by
 decide +kernel
def cuts22866 : List PrefixCut := [⟨68,303791801,303791972⟩,
⟨128,561432366,561432684⟩]
theorem checked22866 : checkPrefixCuts (2^48) 3001024513 9 Manual.Count131072.C022866.packed 128 cuts22866 = true := by
 decide +kernel
def pointBounds22866 : List (Nat × Nat × Nat) := [(3001094144,101751290222575,101751671591266)]
theorem point_links_checked22866 : (cuts22866.take 1).map (fun c => (3001024513-1+2*2^9*c.k,101750986430774+c.lower,101751367799294+c.upper)) = pointBounds22866 := by
 decide +kernel
def cuts22867 : List PrefixCut := [⟨32,141807948,141808032⟩,
⟨124,543682466,543682783⟩,
⟨128,561126440,561126766⟩]
theorem checked22867 : checkPrefixCuts (2^48) 3001155585 9 Manual.Count131072.C022867.packed 128 cuts22867 = true := by
 decide +kernel
def pointBounds22867 : List (Nat × Nat × Nat) := [(3001188352,101751689671088,101752071040010),(3001282560,101752091545606,101752472914761)]
theorem point_links_checked22867 : (cuts22867.take 2).map (fun c => (3001155585-1+2*2^9*c.k,101751547863140+c.lower,101751929231978+c.upper)) = pointBounds22867 := by
 decide +kernel
def cuts22868 : List PrefixCut := [⟨88,388450541,388450766⟩,
⟨128,566166085,566166406⟩]
theorem checked22868 : checkPrefixCuts (2^48) 3001286657 9 Manual.Count131072.C022868.packed 128 cuts22868 = true := by
 decide +kernel
def pointBounds22868 : List (Nat × Nat × Nat) := [(3001376768,101752497440121,101752878809510)]
theorem point_links_checked22868 : (cuts22868.take 1).map (fun c => (3001286657-1+2*2^9*c.k,101752108989580+c.lower,101752490358744+c.upper)) = pointBounds22868 := by
 decide +kernel
def cuts22869 : List PrefixCut := [⟨52,225446675,225446802⟩,
⟨128,558451546,558451864⟩]
theorem checked22869 : checkPrefixCuts (2^48) 3001417729 9 Manual.Count131072.C022869.packed 128 cuts22869 = true := by
 decide +kernel
def pointBounds22869 : List (Nat × Nat × Nat) := [(3001470976,101752900602340,101753281971952)]
theorem point_links_checked22869 : (cuts22869.take 1).map (fun c => (3001417729-1+2*2^9*c.k,101752675155665+c.lower,101753056525150+c.upper)) = pointBounds22869 := by
 decide +kernel
def cuts22870 : List PrefixCut := [⟨16,71269992,71270028⟩,
⟨108,476376100,476376374⟩,
⟨128,562740830,562741156⟩]
theorem checked22870 : checkPrefixCuts (2^48) 3001548801 9 Manual.Count131072.C022870.packed 128 cuts22870 = true := by
 decide +kernel
def pointBounds22870 : List (Nat × Nat × Nat) := [(3001565184,101753304877203,101753686247042),(3001659392,101753709983311,101754091353388)]
theorem point_links_checked22870 : (cuts22870.take 2).map (fun c => (3001548801-1+2*2^9*c.k,101753233607211+c.lower,101753614977014+c.upper)) = pointBounds22870 := by
 decide +kernel
def cuts22871 : List PrefixCut := [⟨72,314602789,314602976⟩,
⟨128,557558960,557559284⟩]
theorem checked22871 : checkPrefixCuts (2^48) 3001679873 9 Manual.Count131072.C022871.packed 128 cuts22871 = true := by
 decide +kernel
def pointBounds22871 : List (Nat × Nat × Nat) := [(3001753600,101754110950830,101754492321146)]
theorem point_links_checked22871 : (cuts22871.take 1).map (fun c => (3001679873-1+2*2^9*c.k,101753796348041+c.lower,101754177718170+c.upper)) = pointBounds22871 := by
 decide +kernel
def cuts22872 : List PrefixCut := [⟨36,159405253,159405341⟩,
⟨128,571036857,571037172⟩]
theorem checked22872 : checkPrefixCuts (2^48) 3001810945 9 Manual.Count131072.C022872.packed 128 cuts22872 = true := by
 decide +kernel
def pointBounds22872 : List (Nat × Nat × Nat) := [(3001847808,101754513312254,101754894682795),(3001942016,101754924943858,101755306314626)]
theorem point_links_checked22872 : (cuts22872.take 2).map (fun c => (3001810945-1+2*2^9*c.k,101754353907001+c.lower,101754735277454+c.upper)) = pointBounds22872 := by
 decide +kernel
def cuts22873 : List PrefixCut := [⟨92,400554661,400554890⟩,
⟨128,560322971,560323289⟩]
theorem checked22873 : checkPrefixCuts (2^48) 3001942017 9 Manual.Count131072.C022873.packed 128 cuts22873 = true := by
 decide +kernel
def pointBounds22873 : List (Nat × Nat × Nat) := [(3002036224,101755325498519,101755706869516)]
theorem point_links_checked22873 : (cuts22873.take 1).map (fun c => (3001942017-1+2*2^9*c.k,101754924943858+c.lower,101755306314626+c.upper)) = pointBounds22873 := by
 decide +kernel
def cuts22874 : List PrefixCut := [⟨56,250618562,250618704⟩,
⟨128,562455159,562455483⟩]
theorem checked22874 : checkPrefixCuts (2^48) 3002073089 9 Manual.Count131072.C022874.packed 128 cuts22874 = true := by
 decide +kernel
def pointBounds22874 : List (Nat × Nat × Nat) := [(3002130432,101755735885391,101756117256619)]
theorem point_links_checked22874 : (cuts22874.take 1).map (fun c => (3002073089-1+2*2^9*c.k,101755485266829+c.lower,101755866637915+c.upper)) = pointBounds22874 := by
 decide +kernel
def cuts22875 : List PrefixCut := [⟨20,86817844,86817893⟩,
⟨112,496053952,496054226⟩,
⟨128,568805691,568806005⟩]
theorem checked22875 : checkPrefixCuts (2^48) 3002204161 9 Manual.Count131072.C022875.packed 128 cuts22875 = true := by
 decide +kernel
def pointBounds22875 : List (Nat × Nat × Nat) := [(3002224640,101756134539832,101756515911291),(3002318848,101756543775940,101756925147624)]
theorem point_links_checked22875 : (cuts22875.take 2).map (fun c => (3002204161-1+2*2^9*c.k,101756047721988+c.lower,101756429093398+c.upper)) = pointBounds22875 := by
 decide +kernel
def cuts22876 : List PrefixCut := [⟨76,332252720,332252908⟩,
⟨128,559312155,559312472⟩]
theorem checked22876 : checkPrefixCuts (2^48) 3002335233 9 Manual.Count131072.C022876.packed 128 cuts22876 = true := by
 decide +kernel
def pointBounds22876 : List (Nat × Nat × Nat) := [(3002413056,101756948780399,101757330152311)]
theorem point_links_checked22876 : (cuts22876.take 1).map (fun c => (3002335233-1+2*2^9*c.k,101756616527679+c.lower,101756997899403+c.upper)) = pointBounds22876 := by
 decide +kernel
def cuts22877 : List PrefixCut := [⟨40,179244773,179244866⟩,
⟨128,568381144,568381469⟩]
theorem checked22877 : checkPrefixCuts (2^48) 3002466305 9 Manual.Count131072.C022877.packed 128 cuts22877 = true := by
 decide +kernel
def pointBounds22877 : List (Nat × Nat × Nat) := [(3002507264,101757355084607,101757736456741)]
theorem point_links_checked22877 : (cuts22877.take 1).map (fun c => (3002466305-1+2*2^9*c.k,101757175839834+c.lower,101757557211875+c.upper)) = pointBounds22877 := by
 decide +kernel
def cuts22878 : List PrefixCut := [⟨4,16967616,16967626⟩,
⟨96,417996746,417996985⟩,
⟨128,559544462,559544779⟩]
theorem checked22878 : checkPrefixCuts (2^48) 3002597377 9 Manual.Count131072.C022878.packed 128 cuts22878 = true := by
 decide +kernel
def pointBounds22878 : List (Nat × Nat × Nat) := [(3002601472,101757761188594,101758142560970),(3002695680,101758162217724,101758543590329)]
theorem point_links_checked22878 : (cuts22878.take 2).map (fun c => (3002597377-1+2*2^9*c.k,101757744220978+c.lower,101758125593344+c.upper)) = pointBounds22878 := by
 decide +kernel
def cuts22879 : List PrefixCut := [⟨60,264530777,264530925⟩,
⟨128,562988434,562988755⟩]
theorem checked22879 : checkPrefixCuts (2^48) 3002728449 9 Manual.Count131072.C022879.packed 128 cuts22879 = true := by
 decide +kernel
def pointBounds22879 : List (Nat × Nat × Nat) := [(3002789888,101758568296217,101758949669048)]
theorem point_links_checked22879 : (cuts22879.take 1).map (fun c => (3002728449-1+2*2^9*c.k,101758303765440+c.lower,101758685138123+c.upper)) = pointBounds22879 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000089
