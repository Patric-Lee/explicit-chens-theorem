import PlattPointSubsetKernel
import PlattPointPackets.S2B000089
import PlattPointPackets.S2B000090
import PlattPointPackets.S2B000091
import PlattPointPackets.S2B000092
import PlattPointPackets.S2B000093
import PlattGlobalGrid.S7B000013
namespace ChenEffective.PlattWindow.PointCovers.S7B000013
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000089.points ++ ChenEffective.PlattWindow.PointPackets.S2B000090.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000091.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000092.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000093.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000013.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000013.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000013
