import PlattPointSubsetKernel
import PlattPointPackets.S5B000089
import PlattPointPackets.S5B000090
import PlattPointPackets.S5B000091
import PlattPointPackets.S5B000092
import PlattPointPackets.S5B000093
import PlattPointPackets.S5B000094
import PlattPointPackets.S5B000095
import PlattPointPackets.S5B000096
import PlattPointPackets.S5B000097
import PlattPointPackets.S5B000098
import PlattPointPackets.S5B000099
import PlattPointPackets.S5B000100
import PlattGlobalGrid.S8B000045
namespace ChenEffective.PlattWindow.PointCovers.S8B000045
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((ChenEffective.PlattWindow.PointPackets.S5B000089.points ++ ChenEffective.PlattWindow.PointPackets.S5B000090.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000091.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000092.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000093.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000094.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000095.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000096.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000097.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000098.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000099.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000100.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000045.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000045.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000045
