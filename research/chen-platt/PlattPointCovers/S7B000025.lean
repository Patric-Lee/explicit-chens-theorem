import PlattPointSubsetKernel
import PlattPointPackets.S2B000130
import PlattPointPackets.S2B000131
import PlattPointPackets.S2B000132
import PlattPointPackets.S2B000133
import PlattPointPackets.S2B000134
import PlattGlobalGrid.S7B000025
namespace ChenEffective.PlattWindow.PointCovers.S7B000025
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000130.points ++ ChenEffective.PlattWindow.PointPackets.S2B000131.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000132.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000133.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000134.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000025.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000025.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000025
