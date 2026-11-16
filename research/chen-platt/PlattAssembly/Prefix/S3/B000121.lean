import PlattAssemblyKernel
import PlattCertificates.Count131072.C023872
import PlattCertificates.Count131072.C023873
import PlattCertificates.Count131072.C023874
import PlattCertificates.Count131072.C023875
import PlattCertificates.Count131072.C023876
import PlattCertificates.Count131072.C023877
import PlattCertificates.Count131072.C023878
import PlattCertificates.Count131072.C023879
import PlattCertificates.Count131072.C023880
import PlattCertificates.Count131072.C023881
import PlattCertificates.Count131072.C023882
import PlattCertificates.Count131072.C023883
import PlattCertificates.Count131072.C023884
import PlattCertificates.Count131072.C023885
import PlattCertificates.Count131072.C023886
import PlattCertificates.Count131072.C023887
import PlattCertificates.Count131072.C023888
import PlattCertificates.Count131072.C023889
import PlattCertificates.Count131072.C023890
import PlattCertificates.Count131072.C023891
import PlattCertificates.Count131072.C023892
import PlattCertificates.Count131072.C023893
import PlattCertificates.Count131072.C023894
import PlattCertificates.Count131072.C023895
import PlattCertificates.Count131072.C023896
import PlattCertificates.Count131072.C023897
import PlattCertificates.Count131072.C023898
import PlattCertificates.Count131072.C023899
import PlattCertificates.Count131072.C023900
import PlattCertificates.Count131072.C023901
import PlattCertificates.Count131072.C023902
import PlattCertificates.Count131072.C023903
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000121
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23872 : List PrefixCut := [⟨95,404836796,404837015⟩,
⟨128,545619290,545619588⟩]
theorem checked23872 : checkPrefixCuts (2^48) 3132882945 9 Manual.Count131072.C023872.packed 128 cuts23872 = true := by
 decide +kernel
def pointBounds23872 : List (Nat × Nat × Nat) := [(3132980224,102305446499424,102305828182133)]
theorem point_links_checked23872 : (cuts23872.take 1).map (fun c => (3132882945-1+2*2^9*c.k,102305041662628+c.lower,102305423345118+c.upper)) = pointBounds23872 := by
 decide +kernel
def cuts23873 : List PrefixCut := [⟨63,262155028,262155172⟩,
⟨128,537151510,537151812⟩]
theorem checked23873 : checkPrefixCuts (2^48) 3133014017 9 Manual.Count131072.C023873.packed 128 cuts23873 = true := by
 decide +kernel
def pointBounds23873 : List (Nat × Nat × Nat) := [(3133078528,102305849436946,102306231119878)]
theorem point_links_checked23873 : (cuts23873.take 1).map (fun c => (3133014017-1+2*2^9*c.k,102305587281918+c.lower,102305968964706+c.upper)) = pointBounds23873 := by
 decide +kernel
def cuts23874 : List PrefixCut := [⟨31,130803182,130803255⟩,
⟨127,536410457,536410763⟩,
⟨128,540183488,540183796⟩]
theorem checked23874 : checkPrefixCuts (2^48) 3133145089 9 Manual.Count131072.C023874.packed 128 cuts23874 = true := by
 decide +kernel
def pointBounds23874 : List (Nat × Nat × Nat) := [(3133176832,102306255236610,102306636919773),(3133275136,102306660843885,102307042527281)]
theorem point_links_checked23874 : (cuts23874.take 2).map (fun c => (3133145089-1+2*2^9*c.k,102306124433428+c.lower,102306506116518+c.upper)) = pointBounds23874 := by
 decide +kernel
def cuts23875 : List PrefixCut := [⟨95,406402984,406403212⟩,
⟨128,546449177,546449485⟩]
theorem checked23875 : checkPrefixCuts (2^48) 3133276161 9 Manual.Count131072.C023875.packed 128 cuts23875 = true := by
 decide +kernel
def pointBounds23875 : List (Nat × Nat × Nat) := [(3133373440,102307071019900,102307452703526)]
theorem point_links_checked23875 : (cuts23875.take 1).map (fun c => (3133276161-1+2*2^9*c.k,102306664616916+c.lower,102307046300314+c.upper)) = pointBounds23875 := by
 decide +kernel
def cuts23876 : List PrefixCut := [⟨63,260055998,260056147⟩,
⟨128,531874000,531874302⟩]
theorem checked23876 : checkPrefixCuts (2^48) 3133407233 9 Manual.Count131072.C023876.packed 128 cuts23876 = true := by
 decide +kernel
def pointBounds23876 : List (Nat × Nat × Nat) := [(3133471744,102307471122091,102307852805946)]
theorem point_links_checked23876 : (cuts23876.take 1).map (fun c => (3133407233-1+2*2^9*c.k,102307211066093+c.lower,102307592749799+c.upper)) = pointBounds23876 := by
 decide +kernel
def cuts23877 : List PrefixCut := [⟨31,127912341,127912420⟩,
⟨127,532390884,532391193⟩,
⟨128,536343087,536343398⟩]
theorem checked23877 : checkPrefixCuts (2^48) 3133538305 9 Manual.Count131072.C023877.packed 128 cuts23877 = true := by
 decide +kernel
def pointBounds23877 : List (Nat × Nat × Nat) := [(3133570048,102307870852434,102308252536521),(3133668352,102308275330977,102308657015294)]
theorem point_links_checked23877 : (cuts23877.take 2).map (fun c => (3133538305-1+2*2^9*c.k,102307742940093+c.lower,102308124624101+c.upper)) = pointBounds23877 := by
 decide +kernel
def cuts23878 : List PrefixCut := [⟨95,399615274,399615498⟩,
⟨128,539374425,539374725⟩]
theorem checked23878 : checkPrefixCuts (2^48) 3133669377 9 Manual.Count131072.C023878.packed 128 cuts23878 = true := by
 decide +kernel
def pointBounds23878 : List (Nat × Nat × Nat) := [(3133766656,102308678898454,102309060582997)]
theorem point_links_checked23878 : (cuts23878.take 1).map (fun c => (3133669377-1+2*2^9*c.k,102308279283180+c.lower,102308660967499+c.upper)) = pointBounds23878 := by
 decide +kernel
def cuts23879 : List PrefixCut := [⟨63,263346659,263346807⟩,
⟨128,536567598,536567902⟩]
theorem checked23879 : checkPrefixCuts (2^48) 3133800449 9 Manual.Count131072.C023879.packed 128 cuts23879 = true := by
 decide +kernel
def pointBounds23879 : List (Nat × Nat × Nat) := [(3133864960,102309082004264,102309463689031)]
theorem point_links_checked23879 : (cuts23879.take 1).map (fun c => (3133800449-1+2*2^9*c.k,102308818657605+c.lower,102309200342224+c.upper)) = pointBounds23879 := by
 decide +kernel
def cuts23880 : List PrefixCut := [⟨31,129423152,129423228⟩,
⟨127,540676679,540676984⟩,
⟨128,544538575,544538882⟩]
theorem checked23880 : checkPrefixCuts (2^48) 3133931521 9 Manual.Count131072.C023880.packed 128 cuts23880 = true := by
 decide +kernel
def pointBounds23880 : List (Nat × Nat × Nat) := [(3133963264,102309484648355,102309866333354),(3134061568,102309895901882,102310277587110)]
theorem point_links_checked23880 : (cuts23880.take 2).map (fun c => (3133931521-1+2*2^9*c.k,102309355225203+c.lower,102309736910126+c.upper)) = pointBounds23880 := by
 decide +kernel
def cuts23881 : List PrefixCut := [⟨95,400193906,400194137⟩,
⟨128,535175700,535176006⟩]
theorem checked23881 : checkPrefixCuts (2^48) 3134062593 9 Manual.Count131072.C023881.packed 128 cuts23881 = true := by
 decide +kernel
def pointBounds23881 : List (Nat × Nat × Nat) := [(3134159872,102310299957684,102310681643145)]
theorem point_links_checked23881 : (cuts23881.take 1).map (fun c => (3134062593-1+2*2^9*c.k,102309899763778+c.lower,102310281449008+c.upper)) = pointBounds23881 := by
 decide +kernel
def cuts23882 : List PrefixCut := [⟨63,262415564,262415719⟩,
⟨128,541708977,541709291⟩]
theorem checked23882 : checkPrefixCuts (2^48) 3134193665 9 Manual.Count131072.C023882.packed 128 cuts23882 = true := by
 decide +kernel
def pointBounds23882 : List (Nat × Nat × Nat) := [(3134258176,102310697355042,102311079040733)]
theorem point_links_checked23882 : (cuts23882.take 1).map (fun c => (3134193665-1+2*2^9*c.k,102310434939478+c.lower,102310816625014+c.upper)) = pointBounds23882 := by
 decide +kernel
def cuts23883 : List PrefixCut := [⟨31,128868074,128868148⟩,
⟨127,544560067,544560375⟩,
⟨128,548690879,548691189⟩]
theorem checked23883 : checkPrefixCuts (2^48) 3134324737 9 Manual.Count131072.C023883.packed 128 cuts23883 = true := by
 decide +kernel
def pointBounds23883 : List (Nat × Nat × Nat) := [(3134356480,102311105516529,102311487202453),(3134454784,102311521208522,102311902894680)]
theorem point_links_checked23883 : (cuts23883.take 2).map (fun c => (3134324737-1+2*2^9*c.k,102310976648455+c.lower,102311358334305+c.upper)) = pointBounds23883 := by
 decide +kernel
def cuts23884 : List PrefixCut := [⟨95,392241447,392241674⟩,
⟨128,529630817,529631118⟩]
theorem checked23884 : checkPrefixCuts (2^48) 3134455809 9 Manual.Count131072.C023884.packed 128 cuts23884 = true := by
 decide +kernel
def pointBounds23884 : List (Nat × Nat × Nat) := [(3134553088,102311917580781,102312299267168)]
theorem point_links_checked23884 : (cuts23884.take 1).map (fun c => (3134455809-1+2*2^9*c.k,102311525339334+c.lower,102311907025494+c.upper)) = pointBounds23884 := by
 decide +kernel
def cuts23885 : List PrefixCut := [⟨63,259060233,259060378⟩,
⟨128,530326969,530327266⟩]
theorem checked23885 : checkPrefixCuts (2^48) 3134586881 9 Manual.Count131072.C023885.packed 128 cuts23885 = true := by
 decide +kernel
def pointBounds23885 : List (Nat × Nat × Nat) := [(3134651392,102312314030384,102312695716990)]
theorem point_links_checked23885 : (cuts23885.take 1).map (fun c => (3134586881-1+2*2^9*c.k,102312054970151+c.lower,102312436656612+c.upper)) = pointBounds23885 := by
 decide +kernel
def cuts23886 : List PrefixCut := [⟨31,130737560,130737636⟩,
⟨127,536859584,536859887⟩,
⟨128,541528612,541528917⟩]
theorem checked23886 : checkPrefixCuts (2^48) 3134717953 9 Manual.Count131072.C023886.packed 128 cuts23886 = true := by
 decide +kernel
def pointBounds23886 : List (Nat × Nat × Nat) := [(3134749696,102312716034680,102313097721514),(3134848000,102313122156704,102313503843765)]
theorem point_links_checked23886 : (cuts23886.take 2).map (fun c => (3134717953-1+2*2^9*c.k,102312585297120+c.lower,102312966983878+c.upper)) = pointBounds23886 := by
 decide +kernel
def cuts23887 : List PrefixCut := [⟨95,397220318,397220546⟩,
⟨128,531898894,531899196⟩]
theorem checked23887 : checkPrefixCuts (2^48) 3134849025 9 Manual.Count131072.C023887.packed 128 cuts23887 = true := by
 decide +kernel
def pointBounds23887 : List (Nat × Nat × Nat) := [(3134946304,102313524046050,102313905733341)]
theorem point_links_checked23887 : (cuts23887.take 1).map (fun c => (3134849025-1+2*2^9*c.k,102313126825732+c.lower,102313508512795+c.upper)) = pointBounds23887 := by
 decide +kernel
def cuts23888 : List PrefixCut := [⟨63,265851334,265851486⟩,
⟨128,536814675,536814981⟩]
theorem checked23888 : checkPrefixCuts (2^48) 3134980097 9 Manual.Count131072.C023888.packed 128 cuts23888 = true := by
 decide +kernel
def pointBounds23888 : List (Nat × Nat × Nat) := [(3135044608,102313924575960,102314306263477)]
theorem point_links_checked23888 : (cuts23888.take 1).map (fun c => (3134980097-1+2*2^9*c.k,102313658724626+c.lower,102314040411991+c.upper)) = pointBounds23888 := by
 decide +kernel
def cuts23889 : List PrefixCut := [⟨31,128117518,128117589⟩,
⟨127,529969076,529969371⟩,
⟨128,533829519,533829816⟩]
theorem checked23889 : checkPrefixCuts (2^48) 3135111169 9 Manual.Count131072.C023889.packed 128 cuts23889 = true := by
 decide +kernel
def pointBounds23889 : List (Nat × Nat × Nat) := [(3135142912,102314323656819,102314705344561),(3135241216,102314725508377,102315107196343)]
theorem point_links_checked23889 : (cuts23889.take 2).map (fun c => (3135111169-1+2*2^9*c.k,102314195539301+c.lower,102314577226972+c.upper)) = pointBounds23889 := by
 decide +kernel
def cuts23890 : List PrefixCut := [⟨95,403275314,403275544⟩,
⟨128,542874585,542874898⟩]
theorem checked23890 : checkPrefixCuts (2^48) 3135242241 9 Manual.Count131072.C023890.packed 128 cuts23890 = true := by
 decide +kernel
def pointBounds23890 : List (Nat × Nat × Nat) := [(3135339520,102315132644134,102315514332332)]
theorem point_links_checked23890 : (cuts23890.take 1).map (fun c => (3135242241-1+2*2^9*c.k,102314729368820+c.lower,102315111056788+c.upper)) = pointBounds23890 := by
 decide +kernel
def cuts23891 : List PrefixCut := [⟨63,263214559,263214704⟩,
⟨128,534054159,534054455⟩]
theorem checked23891 : checkPrefixCuts (2^48) 3135373313 9 Manual.Count131072.C023891.packed 128 cuts23891 = true := by
 decide +kernel
def pointBounds23891 : List (Nat × Nat × Nat) := [(3135437824,102315535457964,102315917146390)]
theorem point_links_checked23891 : (cuts23891.take 1).map (fun c => (3135373313-1+2*2^9*c.k,102315272243405+c.lower,102315653931686+c.upper)) = pointBounds23891 := by
 decide +kernel
def cuts23892 : List PrefixCut := [⟨31,130615001,130615074⟩,
⟨127,537443136,537443436⟩,
⟨128,542110993,542111295⟩]
theorem checked23892 : checkPrefixCuts (2^48) 3135504385 9 Manual.Count131072.C023892.packed 128 cuts23892 = true := by
 decide +kernel
def pointBounds23892 : List (Nat × Nat × Nat) := [(3135536128,102315936912565,102316318601215),(3135634432,102316343740700,102316725429577)]
theorem point_links_checked23892 : (cuts23892.take 2).map (fun c => (3135504385-1+2*2^9*c.k,102315806297564+c.lower,102316187986141+c.upper)) = pointBounds23892 := by
 decide +kernel
def cuts23893 : List PrefixCut := [⟨95,396312712,396312939⟩,
⟨128,535714955,535715258⟩]
theorem checked23893 : checkPrefixCuts (2^48) 3135635457 9 Manual.Count131072.C023893.packed 128 cuts23893 = true := by
 decide +kernel
def pointBounds23893 : List (Nat × Nat × Nat) := [(3135732736,102316744721269,102317126410375)]
theorem point_links_checked23893 : (cuts23893.take 1).map (fun c => (3135635457-1+2*2^9*c.k,102316348408557+c.lower,102316730097436+c.upper)) = pointBounds23893 := by
 decide +kernel
def cuts23894 : List PrefixCut := [⟨63,261835131,261835274⟩,
⟨128,539642077,539642376⟩]
theorem checked23894 : checkPrefixCuts (2^48) 3135766529 9 Manual.Count131072.C023894.packed 128 cuts23894 = true := by
 decide +kernel
def pointBounds23894 : List (Nat × Nat × Nat) := [(3135831040,102317145958643,102317527647968)]
theorem point_links_checked23894 : (cuts23894.take 1).map (fun c => (3135766529-1+2*2^9*c.k,102316884123512+c.lower,102317265812694+c.upper)) = pointBounds23894 := by
 decide +kernel
def cuts23895 : List PrefixCut := [⟨31,132932350,132932425⟩,
⟨127,531002968,531003268⟩,
⟨128,534952198,534952500⟩]
theorem checked23895 : checkPrefixCuts (2^48) 3135897601 9 Manual.Count131072.C023895.packed 128 cuts23895 = true := by
 decide +kernel
def pointBounds23895 : List (Nat × Nat × Nat) := [(3135929344,102317556697939,102317938387495),(3136027648,102317954768557,102318336458338)]
theorem point_links_checked23895 : (cuts23895.take 2).map (fun c => (3135897601-1+2*2^9*c.k,102317423765589+c.lower,102317805455070+c.upper)) = pointBounds23895 := by
 decide +kernel
def cuts23896 : List PrefixCut := [⟨95,398596759,398596990⟩,
⟨128,536186475,536186786⟩]
theorem checked23896 : checkPrefixCuts (2^48) 3136028673 9 Manual.Count131072.C023896.packed 128 cuts23896 = true := by
 decide +kernel
def pointBounds23896 : List (Nat × Nat × Nat) := [(3136125952,102318357314546,102318739004560)]
theorem point_links_checked23896 : (cuts23896.take 1).map (fun c => (3136028673-1+2*2^9*c.k,102317958717787+c.lower,102318340407570+c.upper)) = pointBounds23896 := by
 decide +kernel
def cuts23897 : List PrefixCut := [⟨63,264135817,264135970⟩,
⟨128,536433252,536433560⟩]
theorem checked23897 : checkPrefixCuts (2^48) 3136159745 9 Manual.Count131072.C023897.packed 128 cuts23897 = true := by
 decide +kernel
def pointBounds23897 : List (Nat × Nat × Nat) := [(3136224256,102318759040079,102319140730326)]
theorem point_links_checked23897 : (cuts23897.take 1).map (fun c => (3136159745-1+2*2^9*c.k,102318494904262+c.lower,102318876594356+c.upper)) = pointBounds23897 := by
 decide +kernel
def cuts23898 : List PrefixCut := [⟨31,131928458,131928532⟩,
⟨127,540269951,540270249⟩,
⟨128,545475101,545475402⟩]
theorem checked23898 : checkPrefixCuts (2^48) 3136290817 9 Manual.Count131072.C023898.packed 128 cuts23898 = true := by
 decide +kernel
def pointBounds23898 : List (Nat × Nat × Nat) := [(3136322560,102319163265972,102319544956448),(3136420864,102319571607465,102319953298165)]
theorem point_links_checked23898 : (cuts23898.take 2).map (fun c => (3136290817-1+2*2^9*c.k,102319031337514+c.lower,102319413027916+c.upper)) = pointBounds23898 := by
 decide +kernel
def cuts23899 : List PrefixCut := [⟨95,396751898,396752121⟩,
⟨128,533068000,533068303⟩]
theorem checked23899 : checkPrefixCuts (2^48) 3136421889 9 Manual.Count131072.C023899.packed 128 cuts23899 = true := by
 decide +kernel
def pointBounds23899 : List (Nat × Nat × Nat) := [(3136519168,102319973564513,102320355255439)]
theorem point_links_checked23899 : (cuts23899.take 1).map (fun c => (3136421889-1+2*2^9*c.k,102319576812615+c.lower,102319958503318+c.upper)) = pointBounds23899 := by
 decide +kernel
def cuts23900 : List PrefixCut := [⟨63,267333303,267333455⟩,
⟨128,537801844,537802146⟩]
theorem checked23900 : checkPrefixCuts (2^48) 3136552961 9 Manual.Count131072.C023900.packed 128 cuts23900 = true := by
 decide +kernel
def pointBounds23900 : List (Nat × Nat × Nat) := [(3136617472,102320377213918,102320758905076)]
theorem point_links_checked23900 : (cuts23900.take 1).map (fun c => (3136552961-1+2*2^9*c.k,102320109880615+c.lower,102320491571621+c.upper)) = pointBounds23900 := by
 decide +kernel
def cuts23901 : List PrefixCut := [⟨31,136129507,136129585⟩,
⟨127,532395426,532395728⟩,
⟨128,536433398,536433703⟩]
theorem checked23901 : checkPrefixCuts (2^48) 3136684033 9 Manual.Count131072.C023901.packed 128 cuts23901 = true := by
 decide +kernel
def pointBounds23901 : List (Nat × Nat × Nat) := [(3136715776,102320783811966,102321165503352),(3136814080,102321180077885,102321561769495)]
theorem point_links_checked23901 : (cuts23901.take 2).map (fun c => (3136684033-1+2*2^9*c.k,102320647682459+c.lower,102321029373767+c.upper)) = pointBounds23901 := by
 decide +kernel
def cuts23902 : List PrefixCut := [⟨95,401278470,401278692⟩,
⟨128,543948284,543948586⟩]
theorem checked23902 : checkPrefixCuts (2^48) 3136815105 9 Manual.Count131072.C023902.packed 128 cuts23902 = true := by
 decide +kernel
def pointBounds23902 : List (Nat × Nat × Nat) := [(3136912384,102321585394327,102321967086162)]
theorem point_links_checked23902 : (cuts23902.take 1).map (fun c => (3136815105-1+2*2^9*c.k,102321184115857+c.lower,102321565807470+c.upper)) = pointBounds23902 := by
 decide +kernel
def cuts23903 : List PrefixCut := [⟨63,264966899,264967050⟩,
⟨128,534414550,534414848⟩]
theorem checked23903 : checkPrefixCuts (2^48) 3136946177 9 Manual.Count131072.C023903.packed 128 cuts23903 = true := by
 decide +kernel
def pointBounds23903 : List (Nat × Nat × Nat) := [(3137010688,102321993031040,102322374723106)]
theorem point_links_checked23903 : (cuts23903.take 1).map (fun c => (3136946177-1+2*2^9*c.k,102321728064141+c.lower,102322109756056+c.upper)) = pointBounds23903 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000121
