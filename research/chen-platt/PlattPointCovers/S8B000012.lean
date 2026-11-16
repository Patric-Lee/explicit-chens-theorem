import PlattPointSubsetKernel
import PlattPointPackets.S4B000089
import PlattPointPackets.S4B000090
import PlattPointPackets.S4B000091
import PlattPointPackets.S4B000092
import PlattPointPackets.S4B000093
import PlattPointPackets.S4B000094
import PlattPointPackets.S4B000095
import PlattPointPackets.S4B000096
import PlattPointPackets.S4B000097
import PlattGlobalGrid.S8B000012
namespace ChenEffective.PlattWindow.PointCovers.S8B000012
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((ChenEffective.PlattWindow.PointPackets.S4B000089.points ++ ChenEffective.PlattWindow.PointPackets.S4B000090.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000091.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000092.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000093.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000094.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000095.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000096.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000097.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000012.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000012.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000012
